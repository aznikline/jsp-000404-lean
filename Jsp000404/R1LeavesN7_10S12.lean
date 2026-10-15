import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8892 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8893 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8894 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h8895 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h8896 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 2 3 5 (by decide) (by decide) with h8897 | h8897
  · rcases m.htr 2 4 5 (by decide) (by decide) with h8898 | h8898
    · rcases m.htr 3 4 5 (by decide) (by decide) with h8899 | h8899
      · rcases h2bigk with h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c | h8900c
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h0, hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8896, h8899, hc02, hc45, hlam, hphi, ht0b, ht5b, p8900_1]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          rcases p8900_3 (m.d 0 2) (by simp) with h8904 | h8904
          · rcases p8900_3 (m.d 1 2) (by simp) with h8905 | h8905
            · rcases p8900_3 (m.d 2 3) (by simp) with h8906 | h8906
              · linarith only [h8886, h8906, hlam]
              · linarith only [h8896, h8906, hlam]
            · linarith only [h8892, h8905, hlam]
          · linarith only [h8904, hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          rcases p8900_3 (m.d 0 2) (by simp) with h8911 | h8911
          · rcases p8900_3 (m.d 1 2) (by simp) with h8912 | h8912
            · rcases p8900_3 (m.d 2 3) (by simp) with h8913 | h8913
              · linarith only [h8886, h8913, hlam]
              · linarith only [h8897, h8913, hlam]
            · linarith only [h8893, h8912, hlam]
          · linarith only [h8911, hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8886, h8896, h8899, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8900_1]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8896, h8899, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8900_1]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          rcases p8900_3 (m.d 0 2) (by simp) with h8921 | h8921
          · linarith only [h0, h8921, hlam]
          · linarith only [h8887, h8921, hlam]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          rcases p8900_3 (m.d 0 2) (by simp) with h8924 | h8924
          · linarith only [h0, h8924, hlam]
          · linarith only [h8888, h8924, hlam]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8886, hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8891, hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8886, h8896, h8899, hc02, hc45, hlam, hphi, ht0b, ht5b, p8900_1]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          rcases p8900_3 (m.d 0 2) (by simp) with h8931 | h8931
          · rcases p8900_3 (m.d 1 2) (by simp) with h8932 | h8932
            · rcases p8900_3 (m.d 2 3) (by simp) with h8933 | h8933
              · rcases p8900_3 (m.d 2 4) (by simp) with h8934 | h8934
                · linarith only [h8896, h8934, hlam]
                · linarith only [h8898, h8934, hlam]
              · linarith only [h8897, h8933, hlam]
            · linarith only [h8893, h8932, hlam]
          · linarith only [h8888, h8931, hlam]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8887, hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8892, hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8896, hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          rcases p8900_3 (m.d 0 2) (by simp) with h8944 | h8944
          · rcases p8900_3 (m.d 1 2) (by simp) with h8945 | h8945
            · rcases p8900_3 (m.d 2 3) (by simp) with h8946 | h8946
              · rcases p8900_3 (m.d 2 4) (by simp) with h8947 | h8947
                · rcases p8900_3 (m.d 2 5) (by simp) with h8948 | h8948
                  · linarith only [h8898, h8948, hlam]
                  · rcases h4bigk with h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h6874, hlam, p8950_1]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8889, hc03, hc25, hlam, hphi, ht0b, ht5b, p8900_1, p8950_1]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8899, hc04, hc45, hlam, hphi, ht0b, ht5b, p8950_1]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      rcases p8950_3 (m.d 0 4) (by simp) with h8955 | h8955
                      · rcases p8950_3 (m.d 1 4) (by simp) with h8956 | h8956
                        · rcases p8950_3 (m.d 2 4) (by simp) with h8957 | h8957
                          · linarith only [h8887, h8957, hlam]
                          · linarith only [h8898, h8957, hlam]
                        · linarith only [h8895, h8956, hlam]
                      · linarith only [h8955, hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p8950_1]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8891, h8894, h8897, h8899, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8900_1, p8950_1]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8891, h8894, h8899, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8950_1]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      rcases p8950_3 (m.d 0 4) (by simp) with h8966 | h8966
                      · linarith only [h6874, h8966, hlam]
                      · linarith only [h8890, h8966, hlam]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8887, hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8892, hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8886, h8896, h8899, hc02, hc45, hlam, hphi, ht0b, ht5b, p8950_1]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h0, h8886, h8896, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8950_1]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8889, hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8894, hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8896, hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8889, hc03, hc45, hlam, hphi, ht0b, ht5b, p8950_1]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8890, hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8895, hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8898, hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [h8899, hlam, p8950_0]
                    · have p8950_0 := h8950c.1
                      have p8950_1 := h8950c.2.1
                      have p8950_2 := h8950c.2.2.1
                      have p8950_3 := h8950c.2.2.2
                      linarith only [hlam, p8950_0]
                · linarith only [h8898, h8947, hlam]
              · linarith only [h8897, h8946, hlam]
            · linarith only [h8893, h8945, hlam]
          · linarith only [h8888, h8944, hlam]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8888, hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8893, hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8897, hlam, p8900_0]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [h8898, hlam, p8900_1]
        · have p8900_0 := h8900c.1
          have p8900_1 := h8900c.2.1
          have p8900_2 := h8900c.2.2.1
          have p8900_3 := h8900c.2.2.2
          linarith only [hlam, p8900_0]
      · rcases h2bigk with h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c | h8993c
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h0, hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h0, h8896, h8898, h8899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8993_1]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h0, h8898, h8899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8993_1]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          rcases p8993_3 (m.d 0 2) (by simp) with h8998 | h8998
          · rcases p8993_3 (m.d 1 2) (by simp) with h8999 | h8999
            · rcases p8993_3 (m.d 2 3) (by simp) with h9000 | h9000
              · linarith only [h8886, h9000, hlam]
              · linarith only [h8897, h9000, hlam]
            · linarith only [h8893, h8999, hlam]
          · linarith only [h8998, hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8886, h8896, h8898, h8899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8993_1]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8896, h8898, h8899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8993_1]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8898, h8899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8993_1]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          rcases p8993_3 (m.d 0 2) (by simp) with h9009 | h9009
          · linarith only [h0, h9009, hlam]
          · linarith only [h8888, h9009, hlam]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8886, hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8891, hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8886, h8898, h8899, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8993_1]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h0, h8886, h8898, h8899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8993_1]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8887, hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8892, hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8896, hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h0, h8887, h8898, h8899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8993_1]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8888, hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8893, hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8897, hlam, p8993_0]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [h8898, hlam, p8993_1]
        · have p8993_0 := h8993c.1
          have p8993_1 := h8993c.2.1
          have p8993_2 := h8993c.2.2.1
          have p8993_3 := h8993c.2.2.2
          linarith only [hlam, p8993_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h9027 | h9027
      · linarith only [h8896, h8898, h9027, hlam]
      · rcases h2bigk with h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c | h9029c
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [h0, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          rcases p9029_3 (m.d 0 2) (by simp) with h9032 | h9032
          · rcases p9029_3 (m.d 1 2) (by simp) with h9033 | h9033
            · rcases p9029_3 (m.d 2 3) (by simp) with h9034 | h9034
              · linarith only [h9034, hlam, p9029_0]
              · rcases p9029_3 (m.d 2 4) (by simp) with h9036 | h9036
                · linarith only [h8887, h9036, hlam]
                · rcases p9029_3 (m.d 2 5) (by simp) with h9038 | h9038
                  · linarith only [h8888, h9038, hlam]
                  · rcases h4bigk with h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c | h9040c
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h6874, hlam, p9040_1]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      rcases p9040_3 (m.d 0 4) (by simp) with h9043 | h9043
                      · rcases p9040_3 (m.d 1 4) (by simp) with h9044 | h9044
                        · rcases p9040_3 (m.d 2 4) (by simp) with h9045 | h9045
                          · linarith only [h8887, h9045, hlam]
                          · rcases p9040_3 (m.d 3 4) (by simp) with h9047 | h9047
                            · linarith only [h8889, h9047, hlam]
                            · rcases p9040_3 (m.d 4 5) (by simp) with h9049 | h9049
                              · linarith only [h8890, h9049, hlam]
                              · linarith only [h8898, h9049, hlam]
                        · linarith only [h8892, h9044, hlam]
                      · linarith only [h8887, h9043, hlam]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      rcases p9040_3 (m.d 0 4) (by simp) with h9054 | h9054
                      · rcases p9040_3 (m.d 1 4) (by simp) with h9055 | h9055
                        · rcases p9040_3 (m.d 2 4) (by simp) with h9056 | h9056
                          · linarith only [h8887, h9056, hlam]
                          · linarith only [h8896, h9056, hlam]
                        · linarith only [h8894, h9055, hlam]
                      · linarith only [h8889, h9054, hlam]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h0, h8886, h8889, h8898, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9040_1]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p9040_1]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      rcases p9040_3 (m.d 0 4) (by simp) with h9064 | h9064
                      · linarith only [h6874, h9064, hlam]
                      · linarith only [h8887, h9064, hlam]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      rcases p9040_3 (m.d 0 4) (by simp) with h9067 | h9067
                      · linarith only [h6874, h9067, hlam]
                      · linarith only [h8889, h9067, hlam]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h8891, h8894, h8896, h8898, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9040_1]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h8887, hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h8892, hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h8890, h8898, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p9040_1]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h8898, hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h8889, hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h8894, hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h8896, hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h9027, hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h8890, hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h8895, hlam, p9040_0]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h8890, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p9040_1]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [h6874, h8890, h8891, h8894, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9040_1]
                    · have p9040_0 := h9040c.1
                      have p9040_1 := h9040c.2.1
                      have p9040_2 := h9040c.2.2.1
                      have p9040_3 := h9040c.2.2.2
                      linarith only [hlam, p9040_0]
            · linarith only [h8891, h9033, hlam]
          · linarith only [h9032, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          rcases p9029_3 (m.d 0 2) (by simp) with h9088 | h9088
          · rcases p9029_3 (m.d 1 2) (by simp) with h9089 | h9089
            · rcases p9029_3 (m.d 2 3) (by simp) with h9090 | h9090
              · linarith only [h8886, h9090, hlam]
              · linarith only [h8896, h9090, hlam]
            · linarith only [h8892, h9089, hlam]
          · linarith only [h9088, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          rcases p9029_3 (m.d 0 2) (by simp) with h9095 | h9095
          · rcases p9029_3 (m.d 1 2) (by simp) with h9096 | h9096
            · rcases p9029_3 (m.d 2 3) (by simp) with h9097 | h9097
              · linarith only [h8886, h9097, hlam]
              · linarith only [h8897, h9097, hlam]
            · linarith only [h8893, h9096, hlam]
          · linarith only [h9095, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [h8886, h8896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9029_1]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          rcases p9029_3 (m.d 0 2) (by simp) with h9104 | h9104
          · linarith only [h0, h9104, hlam]
          · linarith only [h8886, h9104, hlam]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          rcases p9029_3 (m.d 0 2) (by simp) with h9107 | h9107
          · linarith only [h0, h9107, hlam]
          · linarith only [h8887, h9107, hlam]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          rcases p9029_3 (m.d 0 2) (by simp) with h9110 | h9110
          · linarith only [h0, h9110, hlam]
          · linarith only [h8888, h9110, hlam]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [h8886, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [h8891, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          rcases p9029_3 (m.d 0 2) (by simp) with h9116 | h9116
          · rcases p9029_3 (m.d 1 2) (by simp) with h9117 | h9117
            · rcases p9029_3 (m.d 2 3) (by simp) with h9118 | h9118
              · rcases p9029_3 (m.d 2 4) (by simp) with h9119 | h9119
                · linarith only [h8896, h9119, hlam]
                · rcases p9029_3 (m.d 2 5) (by simp) with h9121 | h9121
                  · linarith only [h8897, h9121, hlam]
                  · linarith only [h8898, h9121, hlam]
              · linarith only [h8896, h9118, hlam]
            · linarith only [h8892, h9117, hlam]
          · linarith only [h8887, h9116, hlam]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          rcases p9029_3 (m.d 0 2) (by simp) with h9127 | h9127
          · rcases p9029_3 (m.d 1 2) (by simp) with h9128 | h9128
            · rcases p9029_3 (m.d 2 3) (by simp) with h9129 | h9129
              · rcases p9029_3 (m.d 2 4) (by simp) with h9130 | h9130
                · linarith only [h8896, h9130, hlam]
                · rcases p9029_3 (m.d 2 5) (by simp) with h9132 | h9132
                  · linarith only [h8897, h9132, hlam]
                  · rcases h4bigk with h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h6874, hlam, p9134_1]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      rcases p9134_3 (m.d 0 4) (by simp) with h9137 | h9137
                      · rcases p9134_3 (m.d 1 4) (by simp) with h9138 | h9138
                        · rcases p9134_3 (m.d 2 4) (by simp) with h9139 | h9139
                          · linarith only [h8887, h9139, hlam]
                          · rcases p9134_3 (m.d 3 4) (by simp) with h9141 | h9141
                            · linarith only [h8889, h9141, hlam]
                            · rcases p9134_3 (m.d 4 5) (by simp) with h9143 | h9143
                              · linarith only [h8890, h9143, hlam]
                              · linarith only [h8898, h9143, hlam]
                        · linarith only [h8892, h9138, hlam]
                      · linarith only [h8887, h9137, hlam]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      rcases p9134_3 (m.d 0 4) (by simp) with h9148 | h9148
                      · rcases p9134_3 (m.d 1 4) (by simp) with h9149 | h9149
                        · rcases p9134_3 (m.d 2 4) (by simp) with h9150 | h9150
                          · linarith only [h8887, h9150, hlam]
                          · linarith only [h8896, h9150, hlam]
                        · linarith only [h8894, h9149, hlam]
                      · linarith only [h8889, h9148, hlam]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h6874, h8891, h8894, h8896, h8898, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9134_1]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p9134_1]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      rcases p9134_3 (m.d 0 4) (by simp) with h9158 | h9158
                      · linarith only [h6874, h9158, hlam]
                      · linarith only [h8887, h9158, hlam]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      rcases p9134_3 (m.d 0 4) (by simp) with h9161 | h9161
                      · linarith only [h6874, h9161, hlam]
                      · linarith only [h8889, h9161, hlam]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h8891, h8894, h8896, h8898, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9134_1]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h8887, hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h8892, hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h8890, h8898, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p9134_1]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h8898, hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h8889, hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h8894, hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h8896, hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h9027, hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h8890, hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h8895, hlam, p9134_0]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h8890, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p9134_1]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [h6874, h8890, h8891, h8894, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9134_1]
                    · have p9134_0 := h9134c.1
                      have p9134_1 := h9134c.2.1
                      have p9134_2 := h9134c.2.2.1
                      have p9134_3 := h9134c.2.2.2
                      linarith only [hlam, p9134_0]
              · linarith only [h8897, h9129, hlam]
            · linarith only [h8893, h9128, hlam]
          · linarith only [h8888, h9127, hlam]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [h8887, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [h8892, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [h8896, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [h8898, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [h8888, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [h8893, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [h8897, hlam, p9029_0]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          rcases p9029_3 (m.d 0 2) (by simp) with h9191 | h9191
          · rcases p9029_3 (m.d 1 2) (by simp) with h9192 | h9192
            · rcases p9029_3 (m.d 2 3) (by simp) with h9193 | h9193
              · rcases p9029_3 (m.d 2 4) (by simp) with h9194 | h9194
                · linarith only [h8898, h9194, hlam]
                · rcases p9029_3 (m.d 2 5) (by simp) with h9196 | h9196
                  · rcases h4bigk with h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c | h9197c
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h6874, hlam, p9197_1]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      rcases p9197_3 (m.d 0 4) (by simp) with h9200 | h9200
                      · rcases p9197_3 (m.d 1 4) (by simp) with h9201 | h9201
                        · rcases p9197_3 (m.d 2 4) (by simp) with h9202 | h9202
                          · linarith only [h8887, h9202, hlam]
                          · rcases p9197_3 (m.d 3 4) (by simp) with h9204 | h9204
                            · linarith only [h8889, h9204, hlam]
                            · rcases p9197_3 (m.d 4 5) (by simp) with h9206 | h9206
                              · linarith only [h8890, h9206, hlam]
                              · linarith only [h8898, h9206, hlam]
                        · linarith only [h8892, h9201, hlam]
                      · linarith only [h8887, h9200, hlam]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      rcases p9197_3 (m.d 0 4) (by simp) with h9211 | h9211
                      · rcases p9197_3 (m.d 1 4) (by simp) with h9212 | h9212
                        · rcases p9197_3 (m.d 2 4) (by simp) with h9213 | h9213
                          · linarith only [h8887, h9213, hlam]
                          · linarith only [h8896, h9213, hlam]
                        · linarith only [h8894, h9212, hlam]
                      · linarith only [h8889, h9211, hlam]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h6874, h8891, h8894, h8896, h8898, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9197_1]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p9197_1]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      rcases p9197_3 (m.d 0 4) (by simp) with h9221 | h9221
                      · linarith only [h6874, h9221, hlam]
                      · linarith only [h8887, h9221, hlam]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      rcases p9197_3 (m.d 0 4) (by simp) with h9224 | h9224
                      · linarith only [h6874, h9224, hlam]
                      · linarith only [h8889, h9224, hlam]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h8891, h8894, h8896, h8898, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9029_1, p9197_1]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h8887, hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h8892, hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h8889, h8890, h8898, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9029_1, p9197_1]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h8898, hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h8889, hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h8894, hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h8896, hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h9027, hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h8890, hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h8895, hlam, p9197_0]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h6874, h8890, h8891, h8894, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9197_1]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [h6874, h8890, h8891, h8894, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9197_1]
                    · have p9197_0 := h9197c.1
                      have p9197_1 := h9197c.2.1
                      have p9197_2 := h9197c.2.2.1
                      have p9197_3 := h9197c.2.2.2
                      linarith only [hlam, p9197_0]
                  · linarith only [h8898, h9196, hlam]
              · linarith only [h8896, h9193, hlam]
            · linarith only [h8892, h9192, hlam]
          · linarith only [h8887, h9191, hlam]
        · have p9029_0 := h9029c.1
          have p9029_1 := h9029c.2.1
          have p9029_2 := h9029c.2.2.1
          have p9029_3 := h9029c.2.2.2
          linarith only [hlam, p9029_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h9248 | h9248
    · linarith only [h8896, h8897, h9248, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h9250 | h9250
      · linarith only [h8896, h8897, h9248, h9250, hlam]
      · rcases h2bigk with h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c | h9252c
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h0, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          rcases p9252_3 (m.d 0 2) (by simp) with h9255 | h9255
          · rcases p9252_3 (m.d 1 2) (by simp) with h9256 | h9256
            · rcases p9252_3 (m.d 2 3) (by simp) with h9257 | h9257
              · linarith only [h9257, hlam, p9252_0]
              · rcases p9252_3 (m.d 2 4) (by simp) with h9259 | h9259
                · linarith only [h8887, h9259, hlam]
                · rcases p9252_3 (m.d 2 5) (by simp) with h9261 | h9261
                  · linarith only [h8888, h9261, hlam]
                  · linarith only [h8897, h9261, hlam]
            · linarith only [h8891, h9256, hlam]
          · linarith only [h9255, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          rcases p9252_3 (m.d 0 2) (by simp) with h9266 | h9266
          · rcases p9252_3 (m.d 1 2) (by simp) with h9267 | h9267
            · rcases p9252_3 (m.d 2 3) (by simp) with h9268 | h9268
              · linarith only [h8886, h9268, hlam]
              · linarith only [h8896, h9268, hlam]
            · linarith only [h8892, h9267, hlam]
          · linarith only [h9266, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          rcases p9252_3 (m.d 0 2) (by simp) with h9273 | h9273
          · rcases p9252_3 (m.d 1 2) (by simp) with h9274 | h9274
            · rcases p9252_3 (m.d 2 3) (by simp) with h9275 | h9275
              · linarith only [h8886, h9275, hlam]
              · rcases p9252_3 (m.d 2 4) (by simp) with h9277 | h9277
                · linarith only [h8887, h9277, hlam]
                · rcases p9252_3 (m.d 2 5) (by simp) with h9279 | h9279
                  · linarith only [h9279, hlam, p9252_0]
                  · rcases h4bigk with h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h6874, hlam, p9281_1]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      rcases p9281_3 (m.d 0 4) (by simp) with h9284 | h9284
                      · rcases p9281_3 (m.d 1 4) (by simp) with h9285 | h9285
                        · rcases p9281_3 (m.d 2 4) (by simp) with h9286 | h9286
                          · linarith only [h8887, h9286, hlam]
                          · rcases p9281_3 (m.d 3 4) (by simp) with h9288 | h9288
                            · linarith only [h8889, h9288, hlam]
                            · rcases p9281_3 (m.d 4 5) (by simp) with h9290 | h9290
                              · linarith only [h8890, h9290, hlam]
                              · linarith only [h9248, h9290, hlam]
                        · linarith only [h8892, h9285, hlam]
                      · linarith only [h8887, h9284, hlam]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      rcases p9281_3 (m.d 0 4) (by simp) with h9295 | h9295
                      · rcases p9281_3 (m.d 1 4) (by simp) with h9296 | h9296
                        · rcases p9281_3 (m.d 2 4) (by simp) with h9297 | h9297
                          · linarith only [h8887, h9297, hlam]
                          · linarith only [h8896, h9297, hlam]
                        · linarith only [h8894, h9296, hlam]
                      · linarith only [h8889, h9295, hlam]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h6874, h8891, h8894, h8897, h9250, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9281_1]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p9281_1]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      rcases p9281_3 (m.d 0 4) (by simp) with h9305 | h9305
                      · linarith only [h6874, h9305, hlam]
                      · linarith only [h8887, h9305, hlam]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      rcases p9281_3 (m.d 0 4) (by simp) with h9308 | h9308
                      · linarith only [h6874, h9308, hlam]
                      · linarith only [h8889, h9308, hlam]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h8891, h8894, h8896, h8897, h9250, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9281_1]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h8887, hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h8892, hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h0, h8887, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9281_1]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h9248, hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h8889, hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h8894, hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h8896, hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h9250, hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h8890, hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h8895, hlam, p9281_0]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h8890, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p9281_1]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [h6874, h8890, h8891, h8894, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9281_1]
                    · have p9281_0 := h9281c.1
                      have p9281_1 := h9281c.2.1
                      have p9281_2 := h9281c.2.2.1
                      have p9281_3 := h9281c.2.2.2
                      linarith only [hlam, p9281_0]
            · linarith only [h8893, h9274, hlam]
          · linarith only [h9273, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h8886, h8896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9252_1]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          rcases p9252_3 (m.d 0 2) (by simp) with h9331 | h9331
          · linarith only [h0, h9331, hlam]
          · linarith only [h8886, h9331, hlam]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          rcases p9252_3 (m.d 0 2) (by simp) with h9334 | h9334
          · linarith only [h0, h9334, hlam]
          · linarith only [h8887, h9334, hlam]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          rcases p9252_3 (m.d 0 2) (by simp) with h9337 | h9337
          · linarith only [h0, h9337, hlam]
          · linarith only [h8888, h9337, hlam]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h8886, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h8891, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h6874, h8890, h8891, h8894, h8896, h8897, h9250, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9252_1]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h8897, hlam, p9252_1]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h8887, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h8892, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h8896, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h9248, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h8888, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h8893, hlam, p9252_0]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [h0, h8888, h8896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9252_1]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          rcases p9252_3 (m.d 0 2) (by simp) with h9353 | h9353
          · rcases p9252_3 (m.d 1 2) (by simp) with h9354 | h9354
            · rcases p9252_3 (m.d 2 3) (by simp) with h9355 | h9355
              · linarith only [h8897, h9355, hlam]
              · linarith only [h8896, h9355, hlam]
            · linarith only [h8892, h9354, hlam]
          · linarith only [h8887, h9353, hlam]
        · have p9252_0 := h9252c.1
          have p9252_1 := h9252c.2.1
          have p9252_2 := h9252c.2.2.1
          have p9252_3 := h9252c.2.2.2
          linarith only [hlam, p9252_0]

end R2N4
