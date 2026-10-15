import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S71

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h41037 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h41038 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h41039 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h41040 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 2 4 5 (by decide) (by decide) with h41864 | h41864
  · linarith only [h41039, h41040, h41864, hlam]
  · rcases m.htr 3 4 5 (by decide) (by decide) with h41866 | h41866
    · linarith only [h41027, h41031, h41039, h41040, h41864, h41866, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · rcases h1bigk with h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c | h41868c
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h0, hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h33187, hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h36828, hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h39227, hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        rcases p41868_3 (m.d 0 1) (by simp) with h41874 | h41874
        · linarith only [h41874, hlam, p41868_0]
        · rcases p41868_3 (m.d 1 2) (by simp) with h41876 | h41876
          · rcases p41868_3 (m.d 1 3) (by simp) with h41877 | h41877
            · linarith only [h41033, h41877, hlam]
            · linarith only [h33187, h41877, hlam]
          · linarith only [h41876, hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h33187, hc01, hc12, hlam, hphi, p41868_1]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h36828, hc01, hc12, hlam, hphi, p41868_1]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h39227, hc01, hc12, hlam, hphi, p41868_1]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        rcases p41868_3 (m.d 0 1) (by simp) with h41885 | h41885
        · linarith only [h41885, hlam, p41868_0]
        · rcases p41868_3 (m.d 1 2) (by simp) with h41887 | h41887
          · rcases p41868_3 (m.d 1 3) (by simp) with h41888 | h41888
            · rcases p41868_3 (m.d 1 4) (by simp) with h41889 | h41889
              · linarith only [h41036, h41889, hlam]
              · linarith only [h36828, h41889, hlam]
            · linarith only [h41888, hlam, p41868_0]
          · linarith only [h0, h41887, hlam]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h41033, hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h36828, h41032, h41040, h41866, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p41868_1]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h39227, h41033, hc01, hc12, hlam, hphi, p41868_1]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        rcases p41868_3 (m.d 0 1) (by simp) with h41898 | h41898
        · linarith only [h41898, hlam, p41868_0]
        · rcases p41868_3 (m.d 1 2) (by simp) with h41900 | h41900
          · rcases p41868_3 (m.d 1 3) (by simp) with h41901 | h41901
            · rcases p41868_3 (m.d 1 4) (by simp) with h41902 | h41902
              · rcases p41868_3 (m.d 1 5) (by simp) with h41903 | h41903
                · linarith only [h41038, h41903, hlam]
                · linarith only [h39227, h41903, hlam]
              · linarith only [h41902, hlam, p41868_0]
            · linarith only [h33187, h41901, hlam]
          · linarith only [h0, h41900, hlam]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h41034, hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h41036, hlam, p41868_1]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h39227, h41032, h41039, h41040, h41866, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41868_1]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        rcases p41868_3 (m.d 0 1) (by simp) with h41913 | h41913
        · linarith only [h41913, hlam, p41868_0]
        · rcases p41868_3 (m.d 1 2) (by simp) with h41915 | h41915
          · rcases p41868_3 (m.d 1 3) (by simp) with h41916 | h41916
            · rcases p41868_3 (m.d 1 4) (by simp) with h41917 | h41917
              · rcases p41868_3 (m.d 1 5) (by simp) with h41918 | h41918
                · rcases h1emax with h41919 | h41919 | h41919 | h41919 | h41919
                  · rcases h2bigk with h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c | h41920c
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h0, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      rcases p41920_3 (m.d 0 2) (by simp) with h41923 | h41923
                      · rcases p41920_3 (m.d 1 2) (by simp) with h41924 | h41924
                        · rcases p41920_3 (m.d 2 3) (by simp) with h41925 | h41925
                          · linarith only [h41925, hlam, p41920_0]
                          · rcases p41920_3 (m.d 2 4) (by simp) with h41927 | h41927
                            · linarith only [h41028, h41927, hlam]
                            · rcases p41920_3 (m.d 2 5) (by simp) with h41929 | h41929
                              · linarith only [h41029, h41929, hlam]
                              · linarith only [h41040, h41929, hlam]
                        · linarith only [h41033, h41924, hlam]
                      · linarith only [h41923, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      rcases p41920_3 (m.d 0 2) (by simp) with h41934 | h41934
                      · rcases p41920_3 (m.d 1 2) (by simp) with h41935 | h41935
                        · rcases p41920_3 (m.d 2 3) (by simp) with h41936 | h41936
                          · linarith only [h41027, h41936, hlam]
                          · linarith only [h41039, h41936, hlam]
                        · linarith only [h41034, h41935, hlam]
                      · linarith only [h41934, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      rcases p41920_3 (m.d 0 2) (by simp) with h41941 | h41941
                      · rcases p41920_3 (m.d 1 2) (by simp) with h41942 | h41942
                        · rcases p41920_3 (m.d 2 3) (by simp) with h41943 | h41943
                          · linarith only [h41027, h41943, hlam]
                          · rcases p41920_3 (m.d 2 4) (by simp) with h41945 | h41945
                            · linarith only [h41028, h41945, hlam]
                            · rcases p41920_3 (m.d 2 5) (by simp) with h41947 | h41947
                              · linarith only [h41947, hlam, p41920_0]
                              · rcases h4bigk with h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c | h41949c
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h36828, hlam, p41949_1]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  rcases p41949_3 (m.d 0 4) (by simp) with h41952 | h41952
                                  · rcases p41949_3 (m.d 1 4) (by simp) with h41953 | h41953
                                    · rcases p41949_3 (m.d 2 4) (by simp) with h41954 | h41954
                                      · linarith only [h41028, h41954, hlam]
                                      · rcases p41949_3 (m.d 3 4) (by simp) with h41956 | h41956
                                        · linarith only [h41030, h41956, hlam]
                                        · rcases p41949_3 (m.d 4 5) (by simp) with h41958 | h41958
                                          · linarith only [h41032, h41958, hlam]
                                          · linarith only [h41864, h41958, hlam]
                                    · linarith only [h41034, h41953, hlam]
                                  · linarith only [h41028, h41952, hlam]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41032, h41039, h41040, h41866, hlam, p41949_2]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41027, h41030, h41039, h41040, h41866, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p41949_1]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41032, h41033, h41036, h41039, h41040, h41866, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41949_1]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  rcases p41949_3 (m.d 0 4) (by simp) with h41967 | h41967
                                  · linarith only [h36828, h41967, hlam]
                                  · linarith only [h41028, h41967, hlam]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h36828, h41032, h41039, h41040, h41866, hlam, p41949_2]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41039, h41040, h41866, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41949_1]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41028, hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41034, hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41032, h41039, h41040, h41866, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p41949_1]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41864, hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41030, hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41036, hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41039, hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41866, hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41032, hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [h41038, hlam, p41949_0]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  rcases p41949_3 (m.d 0 4) (by simp) with h41984 | h41984
                                  · rcases p41949_3 (m.d 1 4) (by simp) with h41985 | h41985
                                    · rcases p41949_3 (m.d 2 4) (by simp) with h41986 | h41986
                                      · linarith only [h41986, hlam, p41949_0]
                                      · rcases p41949_3 (m.d 3 4) (by simp) with h41988 | h41988
                                        · linarith only [h41866, h41988, hlam]
                                        · rcases p41949_3 (m.d 4 5) (by simp) with h41990 | h41990
                                          · rcases h5bigk with h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c | h41991c
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [hlam, p41991_0]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h39227, hlam, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41029, hlam, p41920_2, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h36828, h41032, h41033, h41036, h41039, h41040, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h36828, h41032, h41033, h41036, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p41949_1, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h39227, h41033, h41036, h41038, hc01, hc12, hlam, hphi, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [hlam, p41991_0]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41033, h41036, h41038, h41039, h41040, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41033, h41036, h41038, h41039, h41040, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41033, h41036, h41038, h41039, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41949_1, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41029, hlam, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41035, hlam, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [hlam, p41991_0]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41040, hlam, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41864, hlam, p41991_0]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41031, hlam, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41037, hlam, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41039, h41040, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [hlam, p41991_0]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41866, hlam, p41991_0]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41032, hlam, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41038, hlam, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h41039, h41040, hc34, hc45, hlam, hphi, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [h36828, h41032, h41033, h41036, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p41991_1]
                                            · have p41991_0 := h41991c.1
                                              have p41991_1 := h41991c.2.1
                                              have p41991_2 := h41991c.2.2.1
                                              have p41991_3 := h41991c.2.2.2
                                              linarith only [hlam, p41991_0]
                                          · linarith only [h41990, hlam, p41949_0]
                                    · linarith only [h41034, h41985, hlam]
                                  · linarith only [h41028, h41984, hlam]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  rcases p41949_3 (m.d 0 4) (by simp) with h42020 | h42020
                                  · rcases p41949_3 (m.d 1 4) (by simp) with h42021 | h42021
                                    · rcases p41949_3 (m.d 2 4) (by simp) with h42022 | h42022
                                      · linarith only [h41864, h42022, hlam]
                                      · linarith only [h41039, h42022, hlam]
                                    · linarith only [h41036, h42021, hlam]
                                  · linarith only [h41030, h42020, hlam]
                                · have p41949_0 := h41949c.1
                                  have p41949_1 := h41949c.2.1
                                  have p41949_2 := h41949c.2.2.1
                                  have p41949_3 := h41949c.2.2.2
                                  linarith only [hlam, p41949_0]
                        · linarith only [h41035, h41942, hlam]
                      · linarith only [h41941, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h41027, h41039, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41920_1]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      rcases p41920_3 (m.d 0 2) (by simp) with h42032 | h42032
                      · linarith only [h0, h42032, hlam]
                      · linarith only [h41027, h42032, hlam]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      rcases p41920_3 (m.d 0 2) (by simp) with h42035 | h42035
                      · linarith only [h0, h42035, hlam]
                      · linarith only [h41028, h42035, hlam]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      rcases p41920_3 (m.d 0 2) (by simp) with h42038 | h42038
                      · linarith only [h0, h42038, hlam]
                      · linarith only [h41029, h42038, hlam]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h41027, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h41033, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h41027, h41030, h41032, h41040, h41866, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p41920_1]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h41040, hlam, p41920_1]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h41028, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h41034, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h41039, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h41864, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h41029, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h41035, hlam, p41920_0]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [h0, h41029, h41039, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41920_1]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      rcases p41920_3 (m.d 0 2) (by simp) with h42054 | h42054
                      · rcases p41920_3 (m.d 1 2) (by simp) with h42055 | h42055
                        · rcases p41920_3 (m.d 2 3) (by simp) with h42056 | h42056
                          · linarith only [h41040, h42056, hlam]
                          · linarith only [h41039, h42056, hlam]
                        · linarith only [h41034, h42055, hlam]
                      · linarith only [h41028, h42054, hlam]
                    · have p41920_0 := h41920c.1
                      have p41920_1 := h41920c.2.1
                      have p41920_2 := h41920c.2.2.1
                      have p41920_3 := h41920c.2.2.2
                      linarith only [hlam, p41920_0]
                  · linarith only [h0, h41919, hc01, hlam]
                  · linarith only [h41036, h41038, h41919, hc01, hlam, p41868_1]
                  · linarith only [h36828, h41032, h41039, h41040, h41866, h41919, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h41919, hc01, hlam, p41868_1]
                · linarith only [h41918, hlam, p41868_0]
              · linarith only [h36828, h41917, hlam]
            · linarith only [h33187, h41916, hlam]
          · linarith only [h0, h41915, hlam]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h41035, hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h41037, hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [h41038, hlam, p41868_0]
      · have p41868_0 := h41868c.1
        have p41868_1 := h41868c.2.1
        have p41868_2 := h41868c.2.2.1
        have p41868_3 := h41868c.2.2.2
        linarith only [hlam, p41868_0]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h41037 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h41038 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h41039 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 2 3 5 (by decide) (by decide) with h41040 | h41040
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037 h41038 h41039 h41040
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037 h41038 h41039 h41040

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h41037 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h41038 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h41039 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h42074 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 2 4 5 (by decide) (by decide) with h42075 | h42075
  · rcases m.htr 3 4 5 (by decide) (by decide) with h42076 | h42076
    · rcases h1bigk with h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c | h42077c
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h0, hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h33187, hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h36828, hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h39227, hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        rcases p42077_3 (m.d 0 1) (by simp) with h42083 | h42083
        · linarith only [h42083, hlam, p42077_0]
        · rcases p42077_3 (m.d 1 2) (by simp) with h42085 | h42085
          · rcases p42077_3 (m.d 1 3) (by simp) with h42086 | h42086
            · linarith only [h41033, h42086, hlam]
            · linarith only [h33187, h42086, hlam]
          · linarith only [h42085, hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h33187, hc01, hc12, hlam, hphi, p42077_1]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h36828, hc01, hc12, hlam, hphi, p42077_1]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h39227, hc01, hc12, hlam, hphi, p42077_1]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        rcases p42077_3 (m.d 0 1) (by simp) with h42094 | h42094
        · linarith only [h42094, hlam, p42077_0]
        · rcases p42077_3 (m.d 1 2) (by simp) with h42096 | h42096
          · rcases p42077_3 (m.d 1 3) (by simp) with h42097 | h42097
            · rcases p42077_3 (m.d 1 4) (by simp) with h42098 | h42098
              · linarith only [h41036, h42098, hlam]
              · linarith only [h36828, h42098, hlam]
            · linarith only [h42097, hlam, p42077_0]
          · linarith only [h0, h42096, hlam]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h41033, hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h36828, hc01, hc13, hlam, hphi, p42077_1]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h39227, h41033, hc01, hc12, hlam, hphi, p42077_1]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        rcases p42077_3 (m.d 0 1) (by simp) with h42107 | h42107
        · linarith only [h42107, hlam, p42077_0]
        · rcases p42077_3 (m.d 1 2) (by simp) with h42109 | h42109
          · rcases p42077_3 (m.d 1 3) (by simp) with h42110 | h42110
            · rcases p42077_3 (m.d 1 4) (by simp) with h42111 | h42111
              · rcases p42077_3 (m.d 1 5) (by simp) with h42112 | h42112
                · linarith only [h41038, h42112, hlam]
                · linarith only [h39227, h42112, hlam]
              · linarith only [h42111, hlam, p42077_0]
            · linarith only [h33187, h42110, hlam]
          · linarith only [h0, h42109, hlam]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h41034, hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h41036, hlam, p42077_1]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h39227, hc01, hc14, hlam, hphi, p42077_1]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        rcases p42077_3 (m.d 0 1) (by simp) with h42122 | h42122
        · linarith only [h42122, hlam, p42077_0]
        · rcases p42077_3 (m.d 1 2) (by simp) with h42124 | h42124
          · rcases p42077_3 (m.d 1 3) (by simp) with h42125 | h42125
            · rcases p42077_3 (m.d 1 4) (by simp) with h42126 | h42126
              · rcases p42077_3 (m.d 1 5) (by simp) with h42127 | h42127
                · rcases h1emax with h42128 | h42128 | h42128 | h42128 | h42128
                  · rcases h2bigk with h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c | h42129c
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h0, hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      rcases p42129_3 (m.d 0 2) (by simp) with h42132 | h42132
                      · rcases p42129_3 (m.d 1 2) (by simp) with h42133 | h42133
                        · rcases p42129_3 (m.d 2 3) (by simp) with h42134 | h42134
                          · linarith only [h42134, hlam, p42129_0]
                          · rcases p42129_3 (m.d 2 4) (by simp) with h42136 | h42136
                            · linarith only [h41028, h42136, hlam]
                            · linarith only [h41039, h42136, hlam]
                        · linarith only [h41033, h42133, hlam]
                      · linarith only [h42132, hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      rcases p42129_3 (m.d 0 2) (by simp) with h42141 | h42141
                      · rcases p42129_3 (m.d 1 2) (by simp) with h42142 | h42142
                        · rcases p42129_3 (m.d 2 3) (by simp) with h42143 | h42143
                          · linarith only [h41027, h42143, hlam]
                          · rcases p42129_3 (m.d 2 4) (by simp) with h42145 | h42145
                            · linarith only [h42145, hlam, p42129_0]
                            · rcases p42129_3 (m.d 2 5) (by simp) with h42147 | h42147
                              · linarith only [h41029, h42147, hlam]
                              · rcases h4bigk with h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c | h42149c
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h36828, hlam, p42149_1]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  rcases p42149_3 (m.d 0 4) (by simp) with h42152 | h42152
                                  · rcases p42149_3 (m.d 1 4) (by simp) with h42153 | h42153
                                    · rcases p42149_3 (m.d 2 4) (by simp) with h42154 | h42154
                                      · linarith only [h41028, h42154, hlam]
                                      · rcases p42149_3 (m.d 3 4) (by simp) with h42156 | h42156
                                        · linarith only [h41030, h42156, hlam]
                                        · linarith only [h41039, h42156, hlam]
                                    · linarith only [h41034, h42153, hlam]
                                  · linarith only [h41028, h42152, hlam]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h0, h41027, h41030, h41039, h42074, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p42149_1]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  rcases p42149_3 (m.d 0 4) (by simp) with h42162 | h42162
                                  · rcases p42149_3 (m.d 1 4) (by simp) with h42163 | h42163
                                    · rcases p42149_3 (m.d 2 4) (by simp) with h42164 | h42164
                                      · linarith only [h41028, h42164, hlam]
                                      · linarith only [h42075, h42164, hlam]
                                    · linarith only [h41038, h42163, hlam]
                                  · linarith only [h42162, hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h41030, h41033, h41036, h41039, h42074, h42076, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42149_1]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  rcases p42149_3 (m.d 0 4) (by simp) with h42171 | h42171
                                  · linarith only [h36828, h42171, hlam]
                                  · linarith only [h41028, h42171, hlam]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h41033, h41036, h41039, h42074, h42076, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42149_1]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  rcases p42149_3 (m.d 0 4) (by simp) with h42175 | h42175
                                  · linarith only [h36828, h42175, hlam]
                                  · linarith only [h41032, h42175, hlam]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h41028, hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h41034, hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h41039, hlam, p42149_1]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42129_1, p42149_1]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h41030, hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h41036, hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h41027, h41030, hlam, p42129_2, p42149_1]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  rcases p42149_3 (m.d 0 4) (by simp) with h42187 | h42187
                                  · rcases p42149_3 (m.d 1 4) (by simp) with h42188 | h42188
                                    · rcases p42149_3 (m.d 2 4) (by simp) with h42189 | h42189
                                      · linarith only [h41039, h42189, hlam]
                                      · linarith only [h42075, h42189, hlam]
                                    · linarith only [h41038, h42188, hlam]
                                  · linarith only [h41032, h42187, hlam]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h41032, hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h41038, hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h42075, hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [h42076, hlam, p42149_0]
                                · have p42149_0 := h42149c.1
                                  have p42149_1 := h42149c.2.1
                                  have p42149_2 := h42149c.2.2.1
                                  have p42149_3 := h42149c.2.2.2
                                  linarith only [hlam, p42149_0]
                        · linarith only [h41034, h42142, hlam]
                      · linarith only [h42141, hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      rcases p42129_3 (m.d 0 2) (by simp) with h42201 | h42201
                      · rcases p42129_3 (m.d 1 2) (by simp) with h42202 | h42202
                        · rcases p42129_3 (m.d 2 3) (by simp) with h42203 | h42203
                          · linarith only [h41027, h42203, hlam]
                          · linarith only [h42074, h42203, hlam]
                        · linarith only [h41035, h42202, hlam]
                      · linarith only [h42201, hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h41027, h41030, h41039, h42074, h42076, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42129_1]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      rcases p42129_3 (m.d 0 2) (by simp) with h42210 | h42210
                      · linarith only [h0, h42210, hlam]
                      · linarith only [h41027, h42210, hlam]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      rcases p42129_3 (m.d 0 2) (by simp) with h42213 | h42213
                      · linarith only [h0, h42213, hlam]
                      · linarith only [h41028, h42213, hlam]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      rcases p42129_3 (m.d 0 2) (by simp) with h42216 | h42216
                      · linarith only [h0, h42216, hlam]
                      · linarith only [h41029, h42216, hlam]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h41027, hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h41033, hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h41039, hlam, p42129_1]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h41027, h41030, h41039, hc02, hc25, hlam, hphi, ht0b, ht5b, p42129_1]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h41028, hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h41034, hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h0, h41027, h41030, h41039, h42074, h42076, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42129_1]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      rcases p42129_3 (m.d 0 2) (by simp) with h42228 | h42228
                      · rcases p42129_3 (m.d 1 2) (by simp) with h42229 | h42229
                        · rcases p42129_3 (m.d 2 3) (by simp) with h42230 | h42230
                          · linarith only [h41039, h42230, hlam]
                          · linarith only [h42074, h42230, hlam]
                        · linarith only [h41035, h42229, hlam]
                      · linarith only [h41029, h42228, hlam]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h41029, hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h41035, hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h42074, hlam, p42129_0]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [h42075, hlam, p42129_1]
                    · have p42129_0 := h42129c.1
                      have p42129_1 := h42129c.2.1
                      have p42129_2 := h42129c.2.2.1
                      have p42129_3 := h42129c.2.2.2
                      linarith only [hlam, p42129_0]
                  · linarith only [h0, h42128, hc01, hlam]
                  · linarith only [h33187, h41030, h41039, h42074, h42076, h42128, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h36828, h42128, hc01, hlam]
                  · linarith only [h42128, hc01, hlam, p42077_1]
                · linarith only [h42127, hlam, p42077_0]
              · linarith only [h36828, h42126, hlam]
            · linarith only [h33187, h42125, hlam]
          · linarith only [h0, h42124, hlam]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h41035, hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h41037, hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [h41038, hlam, p42077_0]
      · have p42077_0 := h42077c.1
        have p42077_1 := h42077c.2.1
        have p42077_2 := h42077c.2.2.1
        have p42077_3 := h42077c.2.2.2
        linarith only [hlam, p42077_0]
    · linarith only [h41032, h41039, h42074, h42076, hc04, hc35, hlam, hphi, ht0b, ht5b]
  · linarith only [h41039, h42074, h42075, hlam]

end R2N4
