import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  rcases m.htr 1 2 3 (by decide) (by decide) with h33837 | h33837
  · rcases m.htr 1 2 4 (by decide) (by decide) with h33838 | h33838
    · rcases m.htr 1 2 5 (by decide) (by decide) with h33839 | h33839
      · rcases m.htr 1 3 4 (by decide) (by decide) with h33840 | h33840
        · linarith only [h0, h33187, h33193, h33840, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h33842 | h33842
          · linarith only [h33187, h33775, h33842, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h33844 | h33844
            · rcases m.htr 2 3 4 (by decide) (by decide) with h33845 | h33845
              · linarith only [h33187, h33193, h33837, h33845, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h33847 | h33847
                · linarith only [h33187, h33775, h33837, h33847, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h33849 | h33849
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h33850 | h33850
                    · rcases h1bigk with h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c | h33851c
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h0, hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        rcases p33851_3 (m.d 0 1) (by simp) with h33854 | h33854
                        · rcases p33851_3 (m.d 1 2) (by simp) with h33855 | h33855
                          · rcases p33851_3 (m.d 1 3) (by simp) with h33856 | h33856
                            · linarith only [h33856, hlam, p33851_0]
                            · rcases p33851_3 (m.d 1 4) (by simp) with h33858 | h33858
                              · linarith only [h33188, h33858, hlam]
                              · linarith only [h33840, h33858, hlam]
                          · linarith only [h33837, h33855, hlam]
                        · linarith only [h33854, hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h0, h33838, h33849, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p33851_1]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        rcases p33851_3 (m.d 0 1) (by simp) with h33864 | h33864
                        · rcases p33851_3 (m.d 1 2) (by simp) with h33865 | h33865
                          · rcases p33851_3 (m.d 1 3) (by simp) with h33866 | h33866
                            · linarith only [h33187, h33866, hlam]
                            · rcases p33851_3 (m.d 1 4) (by simp) with h33868 | h33868
                              · linarith only [h33188, h33868, hlam]
                              · linarith only [h33844, h33868, hlam]
                          · linarith only [h33839, h33865, hlam]
                        · linarith only [h33864, hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h33188, h33838, h33849, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p33851_1]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        rcases p33851_3 (m.d 0 1) (by simp) with h33875 | h33875
                        · linarith only [h0, h33875, hlam]
                        · linarith only [h33187, h33875, hlam]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        rcases p33851_3 (m.d 0 1) (by simp) with h33878 | h33878
                        · linarith only [h0, h33878, hlam]
                        · linarith only [h33188, h33878, hlam]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        rcases p33851_3 (m.d 0 1) (by simp) with h33881 | h33881
                        · linarith only [h0, h33881, hlam]
                        · linarith only [h33189, h33881, hlam]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h33187, hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h33837, hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h33840, hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h33842, hlam, p33851_1]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h33188, hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h33838, hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h0, h33188, h33837, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33851_1]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h0, h33188, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p33851_1]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h33189, hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h33839, hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h0, h33189, h33837, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33851_1]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [h33844, hlam, p33851_0]
                      · have p33851_0 := h33851c.1
                        have p33851_1 := h33851c.2.1
                        have p33851_2 := h33851c.2.2.1
                        have p33851_3 := h33851c.2.2.2
                        linarith only [hlam, p33851_0]
                    · linarith only [h33191, h33193, h33849, h33850, hlam]
                  · linarith only [h0, h33188, h33844, h33849, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h33901 | h33901
              · linarith only [h0, h33187, h33193, h33836, h33837, h33844, h33901, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h33903 | h33903
                · linarith only [h33190, h33193, h33775, h33836, h33840, h33844, h33903, hc13, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h33905 | h33905
                  · linarith only [h33838, h33844, h33905, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h33907 | h33907
                    · rcases h1bigk with h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c | h33908c
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h0, hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        rcases p33908_3 (m.d 0 1) (by simp) with h33911 | h33911
                        · rcases p33908_3 (m.d 1 2) (by simp) with h33912 | h33912
                          · rcases p33908_3 (m.d 1 3) (by simp) with h33913 | h33913
                            · linarith only [h33913, hlam, p33908_0]
                            · rcases p33908_3 (m.d 1 4) (by simp) with h33915 | h33915
                              · linarith only [h33188, h33915, hlam]
                              · linarith only [h33840, h33915, hlam]
                          · linarith only [h33837, h33912, hlam]
                        · linarith only [h33911, hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        rcases p33908_3 (m.d 0 1) (by simp) with h33920 | h33920
                        · rcases p33908_3 (m.d 1 2) (by simp) with h33921 | h33921
                          · rcases p33908_3 (m.d 1 3) (by simp) with h33922 | h33922
                            · linarith only [h33187, h33922, hlam]
                            · rcases p33908_3 (m.d 1 4) (by simp) with h33924 | h33924
                              · linarith only [h33924, hlam, p33908_0]
                              · rcases p33908_3 (m.d 1 5) (by simp) with h33926 | h33926
                                · linarith only [h33189, h33926, hlam]
                                · linarith only [h33844, h33926, hlam]
                          · linarith only [h33838, h33921, hlam]
                        · linarith only [h33920, hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        rcases p33908_3 (m.d 0 1) (by simp) with h33931 | h33931
                        · rcases p33908_3 (m.d 1 2) (by simp) with h33932 | h33932
                          · rcases p33908_3 (m.d 1 3) (by simp) with h33933 | h33933
                            · linarith only [h33187, h33933, hlam]
                            · rcases p33908_3 (m.d 1 4) (by simp) with h33935 | h33935
                              · linarith only [h33188, h33935, hlam]
                              · rcases p33908_3 (m.d 1 5) (by simp) with h33937 | h33937
                                · linarith only [h33937, hlam, p33908_0]
                                · rcases h1emax with h33939 | h33939 | h33939 | h33939 | h33939
                                  · linarith only [h33837, h33840, h33844, h33939, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33908_1]
                                  · linarith only [h0, h33837, h33840, h33844, h33939, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33908_1]
                                  · rcases h2bigk with h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c | h33942c
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h0, hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      rcases p33942_3 (m.d 0 2) (by simp) with h33945 | h33945
                                      · rcases p33942_3 (m.d 1 2) (by simp) with h33946 | h33946
                                        · rcases p33942_3 (m.d 2 3) (by simp) with h33947 | h33947
                                          · linarith only [h33947, hlam, p33942_0]
                                          · rcases p33942_3 (m.d 2 4) (by simp) with h33949 | h33949
                                            · linarith only [h33191, h33949, hlam]
                                            · linarith only [h33901, h33949, hlam]
                                        · linarith only [h33837, h33946, hlam]
                                      · linarith only [h33945, hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      rcases p33942_3 (m.d 0 2) (by simp) with h33954 | h33954
                                      · rcases p33942_3 (m.d 1 2) (by simp) with h33955 | h33955
                                        · rcases p33942_3 (m.d 2 3) (by simp) with h33956 | h33956
                                          · linarith only [h33190, h33956, hlam]
                                          · rcases p33942_3 (m.d 2 4) (by simp) with h33958 | h33958
                                            · linarith only [h33958, hlam, p33942_0]
                                            · rcases p33942_3 (m.d 2 5) (by simp) with h33960 | h33960
                                              · linarith only [h33192, h33960, hlam]
                                              · linarith only [h33905, h33960, hlam]
                                        · linarith only [h33838, h33955, hlam]
                                      · linarith only [h33954, hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      rcases p33942_3 (m.d 0 2) (by simp) with h33965 | h33965
                                      · rcases p33942_3 (m.d 1 2) (by simp) with h33966 | h33966
                                        · rcases p33942_3 (m.d 2 3) (by simp) with h33967 | h33967
                                          · linarith only [h33190, h33967, hlam]
                                          · rcases p33942_3 (m.d 2 4) (by simp) with h33969 | h33969
                                            · linarith only [h33191, h33969, hlam]
                                            · rcases p33942_3 (m.d 2 5) (by simp) with h33971 | h33971
                                              · linarith only [h33971, hlam, p33942_0]
                                              · rcases h4bigk with h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c | h33973c
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [hlam, p33973_0]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  rcases p33973_3 (m.d 0 4) (by simp) with h33975 | h33975
                                                  · rcases p33973_3 (m.d 1 4) (by simp) with h33976 | h33976
                                                    · linarith only [h33188, h33976, hlam]
                                                    · rcases p33973_3 (m.d 2 4) (by simp) with h33978 | h33978
                                                      · linarith only [h33191, h33978, hlam]
                                                      · rcases p33973_3 (m.d 3 4) (by simp) with h33980 | h33980
                                                        · rcases p33973_3 (m.d 4 5) (by simp) with h33981 | h33981
                                                          · linarith only [h33836, h33981, hlam]
                                                          · linarith only [h33844, h33981, hlam]
                                                        · linarith only [h33840, h33980, hlam]
                                                  · linarith only [h33188, h33975, hlam]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  rcases p33973_3 (m.d 0 4) (by simp) with h33986 | h33986
                                                  · rcases p33973_3 (m.d 1 4) (by simp) with h33987 | h33987
                                                    · linarith only [h33188, h33987, hlam]
                                                    · linarith only [h33838, h33987, hlam]
                                                  · linarith only [h33191, h33986, hlam]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33193, hlam, p33973_1]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h0, h33188, h33837, h33840, h33844, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33973_1]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33188, hlam, p33973_0]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [hlam, p33973_0]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33844, hc24, hc45, hlam, hphi, p33973_1]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33840, hlam, p33973_1]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33844, hlam, p33973_0]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33191, hlam, p33973_0]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33838, hlam, p33973_0]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [hlam, p33973_0]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33901, hlam, p33973_1]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33905, hlam, p33973_0]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33836, h33844, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p33973_1]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  rcases p33973_3 (m.d 0 4) (by simp) with h34004 | h34004
                                                  · linarith only [h33193, h34004, hlam]
                                                  · linarith only [h33188, h34004, hlam]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  rcases p33973_3 (m.d 0 4) (by simp) with h34007 | h34007
                                                  · linarith only [h33193, h34007, hlam]
                                                  · linarith only [h33191, h34007, hlam]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [hlam, p33973_0]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33837, h33840, h33844, hc23, hc34, hlam, hphi, p33973_1]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33836, hlam, p33973_0]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h0, h33188, h33836, h33837, h33840, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33973_1]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h0, h33188, h33836, h33901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33973_1]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [h33907, hlam, p33973_0]
                                                · have p33973_0 := h33973c.1
                                                  have p33973_1 := h33973c.2.1
                                                  have p33973_2 := h33973c.2.2.1
                                                  have p33973_3 := h33973c.2.2.2
                                                  linarith only [hlam, p33973_0]
                                        · linarith only [h33839, h33966, hlam]
                                      · linarith only [h33965, hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p33908_1, p33942_1]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h0, h33839, h33901, h33905, hlam, p33908_1, p33942_2]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h0, h33839, h33905, hlam, p33908_1, p33942_2]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h0, h33839, hlam, p33908_1, p33942_2]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h33190, hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h33837, hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h33901, hlam, p33942_1]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h33903, hlam, p33942_1]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h33191, hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h33838, hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h33839, h33905, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p33908_1, p33942_1]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h33905, hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h33192, hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h33839, hlam, p33942_0]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h0, h33839, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33908_1, p33942_1]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [h0, h33839, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p33908_1, p33942_1]
                                    · have p33942_0 := h33942c.1
                                      have p33942_1 := h33942c.2.1
                                      have p33942_2 := h33942c.2.2.1
                                      have p33942_3 := h33942c.2.2.2
                                      linarith only [hlam, p33942_0]
                                  · rcases h2bigk with h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c | h34039c
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h0, hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      rcases p34039_3 (m.d 0 2) (by simp) with h34042 | h34042
                                      · rcases p34039_3 (m.d 1 2) (by simp) with h34043 | h34043
                                        · rcases p34039_3 (m.d 2 3) (by simp) with h34044 | h34044
                                          · linarith only [h34044, hlam, p34039_0]
                                          · rcases p34039_3 (m.d 2 4) (by simp) with h34046 | h34046
                                            · linarith only [h33191, h34046, hlam]
                                            · linarith only [h33901, h34046, hlam]
                                        · linarith only [h33837, h34043, hlam]
                                      · linarith only [h34042, hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      rcases p34039_3 (m.d 0 2) (by simp) with h34051 | h34051
                                      · rcases p34039_3 (m.d 1 2) (by simp) with h34052 | h34052
                                        · rcases p34039_3 (m.d 2 3) (by simp) with h34053 | h34053
                                          · linarith only [h33190, h34053, hlam]
                                          · rcases p34039_3 (m.d 2 4) (by simp) with h34055 | h34055
                                            · linarith only [h34055, hlam, p34039_0]
                                            · rcases p34039_3 (m.d 2 5) (by simp) with h34057 | h34057
                                              · linarith only [h33192, h34057, hlam]
                                              · linarith only [h33905, h34057, hlam]
                                        · linarith only [h33838, h34052, hlam]
                                      · linarith only [h34051, hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      rcases p34039_3 (m.d 0 2) (by simp) with h34062 | h34062
                                      · rcases p34039_3 (m.d 1 2) (by simp) with h34063 | h34063
                                        · rcases p34039_3 (m.d 2 3) (by simp) with h34064 | h34064
                                          · linarith only [h33190, h34064, hlam]
                                          · rcases p34039_3 (m.d 2 4) (by simp) with h34066 | h34066
                                            · linarith only [h33191, h34066, hlam]
                                            · rcases p34039_3 (m.d 2 5) (by simp) with h34068 | h34068
                                              · linarith only [h34068, hlam, p34039_0]
                                              · rcases h4bigk with h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c | h34070c
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [hlam, p34070_0]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  rcases p34070_3 (m.d 0 4) (by simp) with h34072 | h34072
                                                  · rcases p34070_3 (m.d 1 4) (by simp) with h34073 | h34073
                                                    · linarith only [h33188, h34073, hlam]
                                                    · rcases p34070_3 (m.d 2 4) (by simp) with h34075 | h34075
                                                      · linarith only [h33191, h34075, hlam]
                                                      · rcases p34070_3 (m.d 3 4) (by simp) with h34077 | h34077
                                                        · rcases p34070_3 (m.d 4 5) (by simp) with h34078 | h34078
                                                          · linarith only [h33836, h34078, hlam]
                                                          · linarith only [h33844, h34078, hlam]
                                                        · linarith only [h33840, h34077, hlam]
                                                  · linarith only [h33188, h34072, hlam]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  rcases p34070_3 (m.d 0 4) (by simp) with h34083 | h34083
                                                  · rcases p34070_3 (m.d 1 4) (by simp) with h34084 | h34084
                                                    · linarith only [h33188, h34084, hlam]
                                                    · linarith only [h33838, h34084, hlam]
                                                  · linarith only [h33191, h34083, hlam]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33193, hlam, p34070_1]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h0, h33188, h33837, h33840, h33844, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34070_1]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33188, hlam, p34070_0]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [hlam, p34070_0]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h0, h33188, h33901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34070_1]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33840, hlam, p34070_1]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33844, hlam, p34070_0]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33191, hlam, p34070_0]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33838, hlam, p34070_0]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [hlam, p34070_0]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33901, hlam, p34070_1]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33905, hlam, p34070_0]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33836, h33844, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p34070_1]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  rcases p34070_3 (m.d 0 4) (by simp) with h34101 | h34101
                                                  · linarith only [h33193, h34101, hlam]
                                                  · linarith only [h33188, h34101, hlam]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  rcases p34070_3 (m.d 0 4) (by simp) with h34104 | h34104
                                                  · linarith only [h33193, h34104, hlam]
                                                  · linarith only [h33191, h34104, hlam]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [hlam, p34070_0]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33838, h33844, h33901, hc23, hc34, hlam, hphi, p34070_1]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33836, hlam, p34070_0]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h0, h33188, h33836, h33838, h33901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34070_1]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h0, h33188, h33836, h33901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34070_1]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [h33907, hlam, p34070_0]
                                                · have p34070_0 := h34070c.1
                                                  have p34070_1 := h34070c.2.1
                                                  have p34070_2 := h34070c.2.2.1
                                                  have p34070_3 := h34070c.2.2.2
                                                  linarith only [hlam, p34070_0]
                                        · linarith only [h33839, h34063, hlam]
                                      · linarith only [h34062, hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p33908_1, p34039_1]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h0, h33837, h33842, hlam, p33908_1, p34039_2]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h0, h33188, h33836, h33838, h33844, hlam, p34039_2]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h0, h33839, hlam, p33908_1, p34039_2]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h33190, hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h33837, hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h33901, hlam, p34039_1]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h33903, hlam, p34039_1]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h33191, hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h33838, hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h33188, h33836, h33838, h33844, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34039_1]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h33905, hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h33192, hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h33839, hlam, p34039_0]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h0, h33839, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33908_1, p34039_1]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [h0, h33839, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p33908_1, p34039_1]
                                    · have p34039_0 := h34039c.1
                                      have p34039_1 := h34039c.2.1
                                      have p34039_2 := h34039c.2.2.1
                                      have p34039_3 := h34039c.2.2.2
                                      linarith only [hlam, p34039_0]
                                  · rcases h2bigk with h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c | h34136c
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h0, hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      rcases p34136_3 (m.d 0 2) (by simp) with h34139 | h34139
                                      · rcases p34136_3 (m.d 1 2) (by simp) with h34140 | h34140
                                        · rcases p34136_3 (m.d 2 3) (by simp) with h34141 | h34141
                                          · linarith only [h34141, hlam, p34136_0]
                                          · rcases p34136_3 (m.d 2 4) (by simp) with h34143 | h34143
                                            · linarith only [h33191, h34143, hlam]
                                            · linarith only [h33901, h34143, hlam]
                                        · linarith only [h33837, h34140, hlam]
                                      · linarith only [h34139, hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      rcases p34136_3 (m.d 0 2) (by simp) with h34148 | h34148
                                      · rcases p34136_3 (m.d 1 2) (by simp) with h34149 | h34149
                                        · rcases p34136_3 (m.d 2 3) (by simp) with h34150 | h34150
                                          · linarith only [h33190, h34150, hlam]
                                          · rcases p34136_3 (m.d 2 4) (by simp) with h34152 | h34152
                                            · linarith only [h34152, hlam, p34136_0]
                                            · rcases p34136_3 (m.d 2 5) (by simp) with h34154 | h34154
                                              · linarith only [h33192, h34154, hlam]
                                              · linarith only [h33905, h34154, hlam]
                                        · linarith only [h33838, h34149, hlam]
                                      · linarith only [h34148, hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      rcases p34136_3 (m.d 0 2) (by simp) with h34159 | h34159
                                      · rcases p34136_3 (m.d 1 2) (by simp) with h34160 | h34160
                                        · rcases p34136_3 (m.d 2 3) (by simp) with h34161 | h34161
                                          · linarith only [h33190, h34161, hlam]
                                          · rcases p34136_3 (m.d 2 4) (by simp) with h34163 | h34163
                                            · linarith only [h33191, h34163, hlam]
                                            · rcases p34136_3 (m.d 2 5) (by simp) with h34165 | h34165
                                              · linarith only [h34165, hlam, p34136_0]
                                              · rcases h4bigk with h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c | h34167c
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [hlam, p34167_0]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  rcases p34167_3 (m.d 0 4) (by simp) with h34169 | h34169
                                                  · rcases p34167_3 (m.d 1 4) (by simp) with h34170 | h34170
                                                    · linarith only [h33188, h34170, hlam]
                                                    · rcases p34167_3 (m.d 2 4) (by simp) with h34172 | h34172
                                                      · linarith only [h33191, h34172, hlam]
                                                      · rcases p34167_3 (m.d 3 4) (by simp) with h34174 | h34174
                                                        · rcases p34167_3 (m.d 4 5) (by simp) with h34175 | h34175
                                                          · linarith only [h33836, h34175, hlam]
                                                          · linarith only [h33844, h34175, hlam]
                                                        · linarith only [h33840, h34174, hlam]
                                                  · linarith only [h33188, h34169, hlam]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  rcases p34167_3 (m.d 0 4) (by simp) with h34180 | h34180
                                                  · rcases p34167_3 (m.d 1 4) (by simp) with h34181 | h34181
                                                    · linarith only [h33188, h34181, hlam]
                                                    · linarith only [h33838, h34181, hlam]
                                                  · linarith only [h33191, h34180, hlam]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33193, hlam, p34167_1]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h0, h33188, h33844, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p34167_1]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33188, hlam, p34167_0]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [hlam, p34167_0]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33844, h33901, hc23, hc45, hlam, hphi, ht34, p34167_1]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33840, hlam, p34167_1]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33844, hlam, p34167_0]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33191, hlam, p34167_0]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33838, hlam, p34167_0]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [hlam, p34167_0]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33901, hlam, p34167_1]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33905, hlam, p34167_0]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33836, h33844, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p34167_1]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  rcases p34167_3 (m.d 0 4) (by simp) with h34198 | h34198
                                                  · linarith only [h33193, h34198, hlam]
                                                  · linarith only [h33188, h34198, hlam]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  rcases p34167_3 (m.d 0 4) (by simp) with h34201 | h34201
                                                  · linarith only [h33193, h34201, hlam]
                                                  · linarith only [h33191, h34201, hlam]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [hlam, p34167_0]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33838, h33844, h33901, hc23, hc34, hlam, hphi, p34167_1]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33836, hlam, p34167_0]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h0, h33188, h33836, h33838, h33901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34167_1]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h0, h33188, h33836, h33901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34167_1]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [h33907, hlam, p34167_0]
                                                · have p34167_0 := h34167c.1
                                                  have p34167_1 := h34167c.2.1
                                                  have p34167_2 := h34167c.2.2.1
                                                  have p34167_3 := h34167c.2.2.2
                                                  linarith only [hlam, p34167_0]
                                        · linarith only [h33839, h34160, hlam]
                                      · linarith only [h34159, hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p33908_1, p34136_1]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h0, h33837, h33842, hlam, p33908_1, p34136_2]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h0, h33188, h33836, h33838, h33844, hlam, p34136_2]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h0, h33839, hlam, p33908_1, p34136_2]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h33190, hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h33837, hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h33901, hlam, p34136_1]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h33903, hlam, p34136_1]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h33191, hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h33838, hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h33188, h33836, h33838, h33844, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34136_1]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h33905, hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h33192, hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h33839, hlam, p34136_0]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h0, h33839, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33908_1, p34136_1]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [h0, h33839, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p33908_1, p34136_1]
                                    · have p34136_0 := h34136c.1
                                      have p34136_1 := h34136c.2.1
                                      have p34136_2 := h34136c.2.2.1
                                      have p34136_3 := h34136c.2.2.2
                                      linarith only [hlam, p34136_0]
                          · linarith only [h33839, h33932, hlam]
                        · linarith only [h33931, hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h33188, h33836, h33844, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p33908_1]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h0, h33188, h33836, h33840, h33844, hlam, p33908_2]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h0, h33188, h33836, h33844, hlam, p33908_2]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        rcases p33908_3 (m.d 0 1) (by simp) with h34239 | h34239
                        · linarith only [h0, h34239, hlam]
                        · linarith only [h33189, h34239, hlam]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h33187, hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h33837, hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h33840, hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h33842, hlam, p33908_1]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h33188, hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h33838, hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h33188, h33836, h33837, h33844, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p33908_1]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h33844, hlam, p33908_1]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h33189, hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h33839, hlam, p33908_0]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h0, h33189, h33837, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33908_1]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [h0, h33188, h33836, h33844, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p33908_1]
                      · have p33908_0 := h33908c.1
                        have p33908_1 := h33908c.2.1
                        have p33908_2 := h33908c.2.2.1
                        have p33908_3 := h33908c.2.2.2
                        linarith only [hlam, p33908_0]
                    · linarith only [h0, h33188, h33193, h33836, h33907, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h33188, h33192, h33836, h33839, hc02, hc45, hlam, hphi, ht0b, ht5b]
    · linarith only [h0, h33191, h33838, hlam]
  · linarith only [h0, h33190, h33837, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  linarith only [h33187, h33193, h34264, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  linarith only [h33187, h33775, h34266, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  linarith only [h33188, h33836, h34268, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  linarith only [h33187, h33193, h34261, h34270, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  linarith only [h33187, h33775, h34261, h34272, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  linarith only [h33188, h33836, h34262, h34274, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 0 1) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 0 1) ∧ (m.d 1 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 2) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h0, hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 0 1) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 0 1) ∧ (m.d 1 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 3) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  rcases p34277_3 (m.d 0 1) (by simp) with h34280 | h34280
  · rcases p34277_3 (m.d 1 2) (by simp) with h34281 | h34281
    · rcases p34277_3 (m.d 1 3) (by simp) with h34282 | h34282
      · linarith only [h34282, hlam, p34277_0]
      · rcases p34277_3 (m.d 1 4) (by simp) with h34284 | h34284
        · linarith only [h33188, h34284, hlam]
        · linarith only [h34264, h34284, hlam]
    · linarith only [h34261, h34281, hlam]
  · linarith only [h34280, hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 0 1) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 0 1) ∧ (m.d 1 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 4) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  rcases p34277_3 (m.d 0 1) (by simp) with h34289 | h34289
  · rcases p34277_3 (m.d 1 2) (by simp) with h34290 | h34290
    · rcases p34277_3 (m.d 1 3) (by simp) with h34291 | h34291
      · linarith only [h33187, h34291, hlam]
      · rcases p34277_3 (m.d 1 4) (by simp) with h34293 | h34293
        · linarith only [h34293, hlam, p34277_0]
        · rcases p34277_3 (m.d 1 5) (by simp) with h34295 | h34295
          · linarith only [h33189, h34295, hlam]
          · linarith only [h34268, h34295, hlam]
    · linarith only [h34262, h34290, hlam]
  · linarith only [h34289, hlam, p34277_0]

end R2N4
