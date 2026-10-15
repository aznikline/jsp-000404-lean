import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_56S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4196000 in
set_option maxHeartbeats 4196000 in
theorem r1l7_10_12_23_L_R_L_I_M_IR_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h828 | h828
  · rcases m.htr 0 2 5 (by decide) (by decide) with h829 | h829
    · rcases m.htr 0 3 4 (by decide) (by decide) with h830 | h830
      · rcases m.htr 0 3 5 (by decide) (by decide) with h831 | h831
        · rcases m.htr 0 4 5 (by decide) (by decide) with h832 | h832
          · rcases m.htr 1 2 3 (by decide) (by decide) with h833 | h833
            · linarith only [h2, h833, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h835 | h835
              · rcases m.htr 1 2 5 (by decide) (by decide) with h836 | h836
                · rcases m.htr 1 3 4 (by decide) (by decide) with h837 | h837
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h838 | h838
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h839 | h839
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h840 | h840
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h841 | h841
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h842 | h842
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h843 | h843
                              · rcases h2bigk with h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h835, h841, h842, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p844_1, u3ehi4]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h2, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h2, h841, h842, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p844_1, u3ehi4]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h2, h841, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p844_1, u3ehi4]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h833, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h841, h842, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p844_1, u3ehi4]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h2, h841, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p844_1, u3ehi4]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p844_1, u0ehi1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h835, h841, h842, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p844_1, u3ehi4]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  rcases p844_3 (m.d 0 2) (by simp) with h858 | h858
                                  · linarith only [h2, h858, hlam]
                                  · linarith only [h828, h858, hlam]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  rcases p844_3 (m.d 0 2) (by simp) with h861 | h861
                                  · linarith only [h2, h861, hlam]
                                  · linarith only [h829, h861, hlam]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h828, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h835, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h840, hlam, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h835, h841, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p844_1, u3ehi4]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h829, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h836, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h841, hlam, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h842, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                              · linarith only [h2, h828, h832, h843, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h2, h835, h839, h840, h842, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h2, h841, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h2, h840, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · linarith only [h2, h828, h832, h837, h839, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h2, h828, h831, h832, h837, h838, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h833, h835, h837, hlam]
                · linarith only [h2, h829, h836, hc12, hc23, hlam, hphi]
              · linarith only [h2, h828, h835, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h883 | h883
            · linarith only [h2, h883, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h885 | h885
              · rcases m.htr 1 2 5 (by decide) (by decide) with h886 | h886
                · rcases m.htr 1 3 4 (by decide) (by decide) with h887 | h887
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h888 | h888
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h889 | h889
                      · linarith only [h832, h889, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h891 | h891
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h892 | h892
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h893 | h893
                            · linarith only [h0, h2, h832, h885, h893, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h895 | h895
                              · linarith only [h0, h2, h832, h886, h891, h893, h895, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                              · rcases h2bigk with h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [hlam, p897_0]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h2, h886, h891, h893, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p897_1, u3ehi3]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h2, hlam, p897_0]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h2, h891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p897_1, u3ehi3]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h2, h891, h893, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p897_1, u3ehi3]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h0, hlam, p897_0]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [hlam, p897_0]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h883, hlam, p897_0]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h0, h891, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p897_1, u3ehi3]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h0, h2, h891, h893, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p897_1, u3ehi3]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p897_1, u0ehi1]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h885, h891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p897_1, u3ehi3]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [hlam, p897_0]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  rcases p897_3 (m.d 0 2) (by simp) with h911 | h911
                                  · linarith only [h2, h911, hlam]
                                  · linarith only [h828, h911, hlam]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  rcases p897_3 (m.d 0 2) (by simp) with h914 | h914
                                  · linarith only [h2, h914, hlam]
                                  · linarith only [h829, h914, hlam]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h828, hlam, p897_0]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h885, hlam, p897_0]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h891, hlam, p897_1]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [hlam, p897_0]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h893, hlam, p897_1]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h829, hlam, p897_0]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h886, hlam, p897_0]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h892, hlam, p897_1]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [h0, h886, h891, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p897_1, u3ehi3]
                                · have p897_0 := h897c.1
                                  have p897_1 := h897c.2.1
                                  have p897_2 := h897c.2.2.1
                                  have p897_3 := h897c.2.2.2
                                  linarith only [hlam, p897_0]
                          · linarith only [h2, h892, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h2, h829, h832, h891, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · linarith only [h887, h888, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h830, h832, h887, hc45, hlam, hphi, ht34, u3ehi1]
                · linarith only [h2, h829, h885, h886, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h2, h828, h885, hc12, hc23, hlam, hphi]
        · linarith only [h830, h831, hc35, hlam, hphi, u3ehi3]
      · linarith only [h2, h828, h830, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h935 | h935
      · rcases m.htr 0 3 5 (by decide) (by decide) with h936 | h936
        · rcases m.htr 0 4 5 (by decide) (by decide) with h937 | h937
          · linarith only [h828, h829, h937, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h939 | h939
            · linarith only [h0, h2, h939, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h941 | h941
              · rcases m.htr 1 2 5 (by decide) (by decide) with h942 | h942
                · linarith only [h0, h829, h942, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h944 | h944
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h945 | h945
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h946 | h946
                      · linarith only [h937, h946, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h948 | h948
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h949 | h949
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h950 | h950
                            · linarith only [h0, h829, h941, h946, h949, h950, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h829, h941, h948, h950, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h0, h2, h941, h948, h949, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h2, h948, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h944, h945, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h935, h937, h944, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h828, h829, h941, hc12, hc25, hlam, hphi]
        · linarith only [h935, h936, hc35, hlam, hphi, u3ehi3]
      · linarith only [h2, h828, h935, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h960 | h960
    · rcases m.htr 0 3 4 (by decide) (by decide) with h961 | h961
      · rcases m.htr 0 3 5 (by decide) (by decide) with h962 | h962
        · rcases m.htr 0 4 5 (by decide) (by decide) with h963 | h963
          · rcases m.htr 1 2 3 (by decide) (by decide) with h964 | h964
            · linarith only [h0, h2, h964, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h966 | h966
              · linarith only [h828, h964, h966, hc13, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h968 | h968
                · rcases m.htr 1 3 4 (by decide) (by decide) with h969 | h969
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h970 | h970
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h971 | h971
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h972 | h972
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h973 | h973
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h974 | h974
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h975 | h975
                              · rcases h2bigk with h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h968, h973, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p976_1, u3ehi4]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h2, hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h828, hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h828, h972, h973, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u3ehi4]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h0, hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h964, hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h966, hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h0, h973, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p976_1, u3ehi4]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p976_1, u0ehi1]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h968, h973, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u3ehi4]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h828, h960, h973, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u3ehi4]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  rcases p976_3 (m.d 0 2) (by simp) with h991 | h991
                                  · linarith only [h2, h991, hlam]
                                  · linarith only [h960, h991, hlam]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h0, h968, h973, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u3ehi4]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h968, h973, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u3ehi4]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h972, hlam, p976_1]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  rcases p976_3 (m.d 0 2) (by simp) with h998 | h998
                                  · linarith only [h828, h998, hlam]
                                  · linarith only [h960, h998, hlam]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h960, hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h968, hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h973, hlam, p976_1]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [h974, hlam, p976_0]
                                · have p976_0 := h976c.1
                                  have p976_1 := h976c.2.1
                                  have p976_2 := h976c.2.2.1
                                  have p976_3 := h976c.2.2.2
                                  linarith only [hlam, p976_0]
                              · linarith only [h1, h969, h971, h975, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1, h828, h968, h969, h971, h973, h974, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h2, h973, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h1, h2, h960, h969, h972, hc03, hlam, hphi, u0ehi4]
                      · linarith only [h966, h968, h971, hlam]
                    · linarith only [h969, h970, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1012 | h1012
                    · linarith only [h1012, h2, h961, h969, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h1012, h964, h968, hlam]
                · linarith only [h2, h960, h968, hc12, hc23, hlam, hphi]
          · linarith only [h828, h960, h963, hlam]
        · linarith only [h961, h962, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1018 | h1018
        · linarith only [h1018, h961, hc34, hlam, hphi, u3ehi4]
        · linarith only [h1018, h2, h960, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1021 | h1021
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1022 | h1022
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1023 | h1023
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1024 | h1024
            · linarith only [h0, h1024, h2, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1026 | h1026
              · linarith only [h1026, h828, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1028 | h1028
                · linarith only [h0, h1028, h960, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1030 | h1030
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1031 | h1031
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1032 | h1032
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1033 | h1033
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1034 | h1034
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1035 | h1035
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1036 | h1036
                              · rcases h2bigk with h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h1033, h1035, h960, hc12, hc23, hlam, hphi, p1037_1]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h2, hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h828, hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h960, hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h0, hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h1024, hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h1026, hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h1028, hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p1037_1, u0ehi1]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  rcases p1037_3 (m.d 0 2) (by simp) with h1049 | h1049
                                  · linarith only [h1049, h2, hlam]
                                  · linarith only [h0, h1049, hlam]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h828, hc23, hlam, hphi, ht01, ht12, p1037_1, u0ehi1]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h960, hc23, hlam, hphi, ht01, ht12, p1037_1, u0ehi1]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p1037_1, u0ehi1]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  rcases p1037_3 (m.d 0 2) (by simp) with h1056 | h1056
                                  · linarith only [h1056, h828, hlam]
                                  · linarith only [h0, h1056, hlam]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h1033, hlam, p1037_1]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h1033, h960, hc23, hlam, hphi, ht01, ht12, p1037_1, u0ehi1]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p1037_1, u0ehi1]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  rcases p1037_3 (m.d 0 2) (by simp) with h1063 | h1063
                                  · linarith only [h1063, h960, hlam]
                                  · linarith only [h0, h1063, hlam]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h1034, hlam, p1037_1]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [h1035, hlam, p1037_0]
                                · have p1037_0 := h1037c.1
                                  have p1037_1 := h1037c.2.1
                                  have p1037_2 := h1037c.2.2.1
                                  have p1037_3 := h1037c.2.2.2
                                  linarith only [hlam, p1037_0]
                              · linarith only [h1, h1030, h1032, h1036, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1, h1030, h1032, h1035, h828, hc01, hlam, hphi, u0ehi1]
                          · linarith only [h1034, h2, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h1, h1030, h1033, h2, hc01, hlam, hphi, u0ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1073 | h1073
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1074 | h1074
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1075 | h1075
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1076 | h1076
                              · linarith only [h1030, h1032, h1076, hlam]
                              · rcases h2bigk with h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h960, hc12, hc25, hlam, hphi, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h2, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h828, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h960, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h0, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1024, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1026, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1028, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p1078_1, u0ehi1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  rcases p1078_3 (m.d 0 2) (by simp) with h1090 | h1090
                                  · linarith only [h1090, h2, hlam]
                                  · linarith only [h0, h1090, hlam]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1023, h1030, h1032, h828, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1078_1, u3ehi3]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h960, hc23, hlam, hphi, ht01, ht12, p1078_1, u0ehi1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p1078_1, u0ehi1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  rcases p1078_3 (m.d 0 2) (by simp) with h1097 | h1097
                                  · linarith only [h1097, h828, hlam]
                                  · linarith only [h0, h1097, hlam]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1073, hlam, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1073, h960, hc23, hlam, hphi, ht01, ht12, p1078_1, u0ehi1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p1078_1, u0ehi1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  rcases p1078_3 (m.d 0 2) (by simp) with h1104 | h1104
                                  · linarith only [h1104, h960, hlam]
                                  · linarith only [h0, h1104, hlam]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1074, hlam, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1075, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                            · linarith only [h1023, h1075, h828, hc04, hlam, hphi, u0ehi1]
                          · linarith only [h1074, h2, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h1021, h1023, h1030, h1032, h1073, h2, hlam]
                    · linarith only [h1030, h1031, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1114 | h1114
                    · linarith only [h1030, h1114, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1116 | h1116
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1117 | h1117
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1118 | h1118
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1119 | h1119
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1120 | h1120
                              · rcases h2bigk with h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h2, hc12, hc23, hlam, hphi, p1121_1]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h2, hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h828, hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h960, hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h0, hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h1024, hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h1026, hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h1028, hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p1121_1, u0ehi1]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  rcases p1121_3 (m.d 0 2) (by simp) with h1133 | h1133
                                  · linarith only [h1133, h2, hlam]
                                  · linarith only [h0, h1133, hlam]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h828, hc23, hlam, hphi, ht01, ht12, p1121_1, u0ehi1]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h960, hc23, hlam, hphi, ht01, ht12, p1121_1, u0ehi1]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p1121_1, u0ehi1]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  rcases p1121_3 (m.d 0 2) (by simp) with h1140 | h1140
                                  · linarith only [h1140, h828, hlam]
                                  · linarith only [h0, h1140, hlam]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h1117, hlam, p1121_1]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h1117, h960, hc23, hlam, hphi, ht01, ht12, p1121_1, u0ehi1]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p1121_1, u0ehi1]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  rcases p1121_3 (m.d 0 2) (by simp) with h1147 | h1147
                                  · linarith only [h1147, h960, hlam]
                                  · linarith only [h0, h1147, hlam]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h1118, hlam, p1121_1]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [h1119, hlam, p1121_0]
                                · have p1121_0 := h1121c.1
                                  have p1121_1 := h1121c.2.1
                                  have p1121_2 := h1121c.2.2.1
                                  have p1121_3 := h1121c.2.2.2
                                  linarith only [hlam, p1121_0]
                              · linarith only [h1021, h1023, h1030, h1120, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h1116, h1119, h828, hc14, hlam, hphi, ht01, u0ehi1]
                          · linarith only [h1021, h1118, h2, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1021, h1117, h2, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1157 | h1157
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1158 | h1158
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1159 | h1159
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1160 | h1160
                              · linarith only [h1030, h1116, h1160, hc34, hlam, hphi, u3ehi1]
                              · linarith only [h1021, h1023, h1030, h1160, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h1021, h1023, h1159, h2, h828, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                          · linarith only [h1158, h2, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h1021, h1157, h2, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1166 | h1166
            · linarith only [h1166, h2, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1168 | h1168
              · linarith only [h1168, h828, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1170 | h1170
                · linarith only [h0, h1170, h960, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1172 | h1172
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1173 | h1173
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1174 | h1174
                      · linarith only [h1023, h1174, h828, hc14, hlam, hphi, ht01, u0ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1176 | h1176
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1177 | h1177
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1178 | h1178
                            · linarith only [h1023, h1176, h1178, h828, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h1178, h828, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                          · linarith only [h1, h1173, h1177, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h1, h1172, h1176, h2, hlam]
                    · linarith only [h1172, h1173, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1021, h1023, h1172, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h1021, h1022, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1186 | h1186
        · linarith only [h1021, h1186, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1188 | h1188
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1189 | h1189
            · linarith only [h0, h1189, h2, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1191 | h1191
              · linarith only [h1191, h828, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1193 | h1193
                · linarith only [h0, h1193, h960, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1195 | h1195
                  · linarith only [h1021, h1195, hc13, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1197 | h1197
                    · linarith only [h1, h1186, h1197, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1199 | h1199
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1200 | h1200
                        · linarith only [h1021, h1200, h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · linarith only [h1200, h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · linarith only [h1021, h1188, h1195, h1199, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1204 | h1204
            · linarith only [h1204, h2, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1206 | h1206
              · linarith only [h1206, h828, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1208 | h1208
                · linarith only [h0, h1208, h960, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1210 | h1210
                  · linarith only [h1, h1186, h1210, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1212 | h1212
                    · linarith only [h1, h1186, h1212, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1214 | h1214
                      · linarith only [h1021, h1188, h1214, h2, hc14, hlam, hphi, ht01, u0ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1216 | h1216
                        · linarith only [h1021, h1216, h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · linarith only [h1216, h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

set_option maxHeartbeats 4196000 in
set_option maxHeartbeats 4196000 in
theorem r1l7_10_12_23_L_R_L_I_M_IR_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_23_L_R_L_I_M_IR_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2
  · exact r1l7_10_12_23_L_R_L_I_M_IR_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2

set_option maxHeartbeats 4196000 in
set_option maxHeartbeats 4196000 in
theorem r1l7_10_12_23_L_R_L_I_M_IR_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1219 | h1219
  · linarith only [h0, h1, h1219, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1221 | h1221
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1222 | h1222
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1223 | h1223
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1224 | h1224
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1225 | h1225
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1226 | h1226
              · linarith only [h0, h1, h1219, h1226, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1228 | h1228
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1229 | h1229
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1230 | h1230
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1231 | h1231
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1232 | h1232
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1233 | h1233
                          · linarith only [h0, h1, h1226, h1228, h1233, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h1, h1226, h1233, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1, h1221, h1225, h1230, h1232, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h1231, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h0, h1, h1221, h1223, h1225, h1230, hc03, hlam, hphi, u0ehi4]
                  · linarith only [h0, h1, h1222, h1226, h1229, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h1221, h1226, h1228, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1241 | h1241
              · linarith only [h0, h1, h1241, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1243 | h1243
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1244 | h1244
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1245 | h1245
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1246 | h1246
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1247 | h1247
                        · linarith only [h0, h1, h1225, h1241, h1243, h1247, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1249 | h1249
                          · linarith only [h0, h1, h1241, h1243, h1249, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h1, h1241, h1249, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h1243, h1245, h1246, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h0, h1, h1245, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h0, h1, h1222, h1243, h1244, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h1, h1221, h1241, h1243, hc12, hc23, hlam, hphi]
          · linarith only [h1223, h1224, hc35, hlam, hphi, u3ehi3]
        · linarith only [h0, h1, h1221, h1223, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1258 | h1258
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1259 | h1259
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1260 | h1260
            · linarith only [h1221, h1222, h1260, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1262 | h1262
              · linarith only [h0, h1, h1262, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1264 | h1264
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1265 | h1265
                  · linarith only [h0, h1, h1222, h1262, h1265, hc02, hc23, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1267 | h1267
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1268 | h1268
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1269 | h1269
                        · linarith only [h0, h1, h1260, h1262, h1264, h1269, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1271 | h1271
                          · linarith only [h0, h1, h1262, h1264, h1271, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h1, h1262, h1271, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h1264, h1267, h1268, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h0, h1, h1267, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1, h1221, h1262, h1264, hc12, hc23, hlam, hphi]
          · linarith only [h1258, h1259, hc35, hlam, hphi, u3ehi3]
        · linarith only [h0, h1, h1221, h1258, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1279 | h1279
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1280 | h1280
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1281 | h1281
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1282 | h1282
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1283 | h1283
              · linarith only [h0, h1, h1283, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1285 | h1285
                · linarith only [h0, h1, h1221, h1279, h1283, h1285, hc23, hlam, hphi, ht01, ht12, u0ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1287 | h1287
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1288 | h1288
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1289 | h1289
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1290 | h1290
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1291 | h1291
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1292 | h1292
                            · linarith only [h0, h1, h1283, h1287, h1292, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                            · linarith only [h0, h1, h1283, h1292, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h1283, h1287, h1289, h1291, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h1285, h1287, h1290, hlam]
                      · linarith only [h1, h1289, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h0, h1, h1279, h1280, h1288, hc03, hlam, hphi, u0ehi4]
                  · linarith only [h0, h1, h1279, h1283, h1287, hc12, hc23, hlam, hphi]
            · linarith only [h1221, h1279, h1282, hlam]
          · linarith only [h1280, h1281, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1302 | h1302
          · linarith only [h1280, h1302, hc34, hlam, hphi, u3ehi4]
          · linarith only [h0, h1, h1279, h1302, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1305 | h1305
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1306 | h1306
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1307 | h1307
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1308 | h1308
              · linarith only [h1219, h1308, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1310 | h1310
                · linarith only [h0, h1, h1221, h1310, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1312 | h1312
                  · linarith only [h0, h1, h1279, h1308, h1312, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1314 | h1314
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1315 | h1315
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1316 | h1316
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1317 | h1317
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1318 | h1318
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1319 | h1319
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1320 | h1320
                                · rcases h2bigk with h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1279, h1319, hc12, hc24, hlam, hphi, p1321_1]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1219, hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1221, hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1279, hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h0, hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1308, hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1310, hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1312, hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p1321_1, u0ehi1]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    rcases p1321_3 (m.d 0 2) (by simp) with h1333 | h1333
                                    · linarith only [h1219, h1333, hlam]
                                    · linarith only [h0, h1333, hlam]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1221, hc23, hlam, hphi, ht01, ht12, p1321_1, u0ehi1]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1279, hc23, hlam, hphi, ht01, ht12, p1321_1, u0ehi1]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [hc24, hlam, hphi, ht01, ht12, p1321_1, u0ehi1]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    rcases p1321_3 (m.d 0 2) (by simp) with h1340 | h1340
                                    · linarith only [h1221, h1340, hlam]
                                    · linarith only [h0, h1340, hlam]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1317, hlam, p1321_1]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1279, h1317, hc23, hlam, hphi, ht01, ht12, p1321_1, u0ehi1]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [hc25, hlam, hphi, ht01, ht12, p1321_1, u0ehi1]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    rcases p1321_3 (m.d 0 2) (by simp) with h1347 | h1347
                                    · linarith only [h1279, h1347, hlam]
                                    · linarith only [h0, h1347, hlam]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1318, hlam, p1321_1]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [h1319, hlam, p1321_0]
                                  · have p1321_0 := h1321c.1
                                    have p1321_1 := h1321c.2.1
                                    have p1321_2 := h1321c.2.2.1
                                    have p1321_3 := h1321c.2.2.2
                                    linarith only [hlam, p1321_0]
                                · rcases h2bigk with h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h0, h1, h1308, hc12, hc23, hlam, hphi, p1353_1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1219, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1221, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1279, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h0, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1308, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1310, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1312, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p1353_1, u0ehi1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    rcases p1353_3 (m.d 0 2) (by simp) with h1365 | h1365
                                    · linarith only [h1219, h1365, hlam]
                                    · linarith only [h0, h1365, hlam]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1221, hc23, hlam, hphi, ht01, ht12, p1353_1, u0ehi1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1279, hc23, hlam, hphi, ht01, ht12, p1353_1, u0ehi1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hc24, hlam, hphi, ht01, ht12, p1353_1, u0ehi1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    rcases p1353_3 (m.d 0 2) (by simp) with h1372 | h1372
                                    · linarith only [h1221, h1372, hlam]
                                    · linarith only [h0, h1372, hlam]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1317, hlam, p1353_1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1279, h1317, hc23, hlam, hphi, ht01, ht12, p1353_1, u0ehi1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hc25, hlam, hphi, ht01, ht12, p1353_1, u0ehi1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    rcases p1353_3 (m.d 0 2) (by simp) with h1379 | h1379
                                    · linarith only [h1279, h1379, hlam]
                                    · linarith only [h0, h1379, hlam]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1318, hlam, p1353_1]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [h1319, hlam, p1353_0]
                                  · have p1353_0 := h1353c.1
                                    have p1353_1 := h1353c.2.1
                                    have p1353_2 := h1353c.2.2.1
                                    have p1353_3 := h1353c.2.2.2
                                    linarith only [hlam, p1353_0]
                              · linarith only [h1, h1221, h1305, h1307, h1308, h1319, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h1, h1308, h1318, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                          · linarith only [h0, h1, h1305, h1308, h1317, hc03, hlam, hphi, u0ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1388 | h1388
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1389 | h1389
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1390 | h1390
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1391 | h1391
                                · linarith only [h1314, h1316, h1391, hlam]
                                · rcases h2bigk with h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h0, h1, h1308, hc12, hc23, hlam, hphi, p1393_1]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1219, hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1221, hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1279, hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h0, hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1308, hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1310, hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1312, hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p1393_1, u0ehi1]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    rcases p1393_3 (m.d 0 2) (by simp) with h1405 | h1405
                                    · linarith only [h1219, h1405, hlam]
                                    · linarith only [h0, h1405, hlam]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1221, hc23, hlam, hphi, ht01, ht12, p1393_1, u0ehi1]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1279, hc23, hlam, hphi, ht01, ht12, p1393_1, u0ehi1]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [hc24, hlam, hphi, ht01, ht12, p1393_1, u0ehi1]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    rcases p1393_3 (m.d 0 2) (by simp) with h1412 | h1412
                                    · linarith only [h1221, h1412, hlam]
                                    · linarith only [h0, h1412, hlam]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1388, hlam, p1393_1]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1279, h1388, hc23, hlam, hphi, ht01, ht12, p1393_1, u0ehi1]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [hc25, hlam, hphi, ht01, ht12, p1393_1, u0ehi1]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    rcases p1393_3 (m.d 0 2) (by simp) with h1419 | h1419
                                    · linarith only [h1279, h1419, hlam]
                                    · linarith only [h0, h1419, hlam]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1389, hlam, p1393_1]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [h1390, hlam, p1393_0]
                                  · have p1393_0 := h1393c.1
                                    have p1393_1 := h1393c.2.1
                                    have p1393_2 := h1393c.2.2.1
                                    have p1393_3 := h1393c.2.2.2
                                    linarith only [hlam, p1393_0]
                              · linarith only [h1221, h1390, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                            · linarith only [h1, h1305, h1307, h1308, h1314, h1316, h1389, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1, h1305, h1307, h1308, h1314, h1316, h1388, hlam]
                      · linarith only [h1, h1315, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h1, h1314, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1430 | h1430
              · linarith only [h0, h1, h1430, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1432 | h1432
                · linarith only [h0, h1, h1221, h1430, h1432, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1434 | h1434
                  · linarith only [h0, h1, h1279, h1430, h1434, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1436 | h1436
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1437 | h1437
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1438 | h1438
                        · linarith only [h1307, h1438, hc14, hlam, hphi, ht01, u0ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1440 | h1440
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1441 | h1441
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1442 | h1442
                              · linarith only [h1221, h1307, h1440, h1442, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h1221, h1442, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                            · linarith only [h0, h1, h1430, h1441, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h1430, h1440, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · linarith only [h1, h1306, h1437, hlam]
                    · linarith only [h1, h1305, h1436, hlam]
          · linarith only [h1305, h1306, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1450 | h1450
          · linarith only [h1305, h1450, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1452 | h1452
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1453 | h1453
              · linarith only [h0, h1, h1453, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1455 | h1455
                · linarith only [h0, h1, h1221, h1305, h1455, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1457 | h1457
                  · linarith only [h0, h1, h1279, h1305, h1457, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1459 | h1459
                    · linarith only [h0, h1, h1305, h1453, h1459, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h1459, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1462 | h1462
              · linarith only [h0, h1, h1462, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1464 | h1464
                · linarith only [h0, h1, h1221, h1305, h1452, h1464, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1466 | h1466
                  · linarith only [h0, h1, h1279, h1305, h1452, h1466, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1468 | h1468
                    · linarith only [h0, h1, h1305, h1462, h1468, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h1468, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

set_option maxHeartbeats 4196000 in
set_option maxHeartbeats 4196000 in
theorem r1l7_10_12_23_L_R_L_I_M_IR_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_23_L_R_L_I_M_IR_x0_x0 m hb0 hb2 hb3 h0 h1
  · exact r1l7_10_12_23_L_R_L_I_M_IR_x0_x1 m hb0 hb2 hb3 h0 h1

end R2N4
