import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8385 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8386 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h8387 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h8388 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h8389 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 2 3 5 (by decide) (by decide) with h8899 | h8899
  · linarith only [h8381, h8389, h8899, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h8901 | h8901
    · rcases m.htr 3 4 5 (by decide) (by decide) with h8902 | h8902
      · rcases h1bigk with h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c | h8903c
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h0, hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h6794, hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h7647, hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h8170, hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          rcases p8903_3 (m.d 0 1) (by simp) with h8909 | h8909
          · linarith only [h8909, hlam, p8903_0]
          · rcases p8903_3 (m.d 1 2) (by simp) with h8911 | h8911
            · rcases p8903_3 (m.d 1 3) (by simp) with h8912 | h8912
              · linarith only [h8383, h8912, hlam]
              · linarith only [h6794, h8912, hlam]
            · linarith only [h8911, hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h6794, h8381, h8899, h8902, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8903_1]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h7647, hc01, hc12, hlam, hphi, p8903_1]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h8170, hc01, hc12, hlam, hphi, p8903_1]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          rcases p8903_3 (m.d 0 1) (by simp) with h8920 | h8920
          · linarith only [h8920, hlam, p8903_0]
          · rcases p8903_3 (m.d 1 2) (by simp) with h8922 | h8922
            · rcases p8903_3 (m.d 1 3) (by simp) with h8923 | h8923
              · rcases p8903_3 (m.d 1 4) (by simp) with h8924 | h8924
                · linarith only [h8386, h8924, hlam]
                · linarith only [h7647, h8924, hlam]
              · linarith only [h8923, hlam, p8903_0]
            · linarith only [h0, h8922, hlam]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h8383, hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h7647, h8381, h8389, h8901, hc13, hlam, hphi, ht01, ht0b, ht5b, p8903_1, u5ehi4]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h8170, h8383, hc01, hc12, hlam, hphi, p8903_1]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          rcases p8903_3 (m.d 0 1) (by simp) with h8933 | h8933
          · linarith only [h8933, hlam, p8903_0]
          · rcases p8903_3 (m.d 1 2) (by simp) with h8935 | h8935
            · rcases p8903_3 (m.d 1 3) (by simp) with h8936 | h8936
              · rcases p8903_3 (m.d 1 4) (by simp) with h8937 | h8937
                · rcases p8903_3 (m.d 1 5) (by simp) with h8938 | h8938
                  · linarith only [h8388, h8938, hlam]
                  · linarith only [h8170, h8938, hlam]
                · linarith only [h8937, hlam, p8903_0]
              · linarith only [h6794, h8936, hlam]
            · linarith only [h0, h8935, hlam]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h8384, hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h8386, hlam, p8903_1]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h8170, hc01, hc14, hlam, hphi, p8903_1]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          rcases p8903_3 (m.d 0 1) (by simp) with h8948 | h8948
          · linarith only [h8948, hlam, p8903_0]
          · rcases p8903_3 (m.d 1 2) (by simp) with h8950 | h8950
            · rcases p8903_3 (m.d 1 3) (by simp) with h8951 | h8951
              · rcases p8903_3 (m.d 1 4) (by simp) with h8952 | h8952
                · rcases p8903_3 (m.d 1 5) (by simp) with h8953 | h8953
                  · rcases h2bigk with h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c | h8954c
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h0, hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      rcases p8954_3 (m.d 0 2) (by simp) with h8957 | h8957
                      · rcases p8954_3 (m.d 1 2) (by simp) with h8958 | h8958
                        · rcases p8954_3 (m.d 2 3) (by simp) with h8959 | h8959
                          · linarith only [h8959, hlam, p8954_0]
                          · rcases p8954_3 (m.d 2 4) (by simp) with h8961 | h8961
                            · linarith only [h8379, h8961, hlam]
                            · linarith only [h8389, h8961, hlam]
                        · linarith only [h8383, h8958, hlam]
                      · linarith only [h8957, hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h0, h8901, hc12, hlam, hphi, ht01, ht0b, ht5b, p8954_1, u5ehi4]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      rcases p8954_3 (m.d 0 2) (by simp) with h8967 | h8967
                      · rcases p8954_3 (m.d 1 2) (by simp) with h8968 | h8968
                        · rcases p8954_3 (m.d 2 3) (by simp) with h8969 | h8969
                          · linarith only [h8378, h8969, hlam]
                          · rcases p8954_3 (m.d 2 4) (by simp) with h8971 | h8971
                            · linarith only [h8379, h8971, hlam]
                            · linarith only [h8901, h8971, hlam]
                        · linarith only [h8385, h8968, hlam]
                      · linarith only [h8967, hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8378, h8381, h8389, h8901, hc12, hlam, hphi, ht01, ht0b, ht5b, p8954_1, u5ehi4]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      rcases p8954_3 (m.d 0 2) (by simp) with h8978 | h8978
                      · linarith only [h0, h8978, hlam]
                      · linarith only [h8378, h8978, hlam]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8901, hc12, hlam, hphi, ht01, ht0b, ht5b, p8954_1, u5ehi4]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      rcases p8954_3 (m.d 0 2) (by simp) with h8982 | h8982
                      · linarith only [h0, h8982, hlam]
                      · linarith only [h8380, h8982, hlam]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8378, hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8383, hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8389, hlam, p8954_1]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8899, hlam, p8954_1]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8379, hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8384, hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      rcases p8954_3 (m.d 0 2) (by simp) with h8992 | h8992
                      · rcases p8954_3 (m.d 1 2) (by simp) with h8993 | h8993
                        · rcases p8954_3 (m.d 2 3) (by simp) with h8994 | h8994
                          · linarith only [h8389, h8994, hlam]
                          · rcases p8954_3 (m.d 2 4) (by simp) with h8996 | h8996
                            · rcases p8954_3 (m.d 2 5) (by simp) with h8997 | h8997
                              · linarith only [h8901, h8997, hlam]
                              · linarith only [h8899, h8997, hlam]
                            · linarith only [h8389, h8996, hlam]
                        · linarith only [h8383, h8993, hlam]
                      · linarith only [h8378, h8992, hlam]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8378, h8381, h8389, h8901, hc02, hlam, hphi, ht0b, ht5b, p8954_1, u5ehi4]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8380, hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8385, hlam, p8954_0]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      rcases p8954_3 (m.d 0 2) (by simp) with h9007 | h9007
                      · rcases p8954_3 (m.d 1 2) (by simp) with h9008 | h9008
                        · rcases p8954_3 (m.d 2 3) (by simp) with h9009 | h9009
                          · linarith only [h8899, h9009, hlam]
                          · rcases p8954_3 (m.d 2 4) (by simp) with h9011 | h9011
                            · rcases p8954_3 (m.d 2 5) (by simp) with h9012 | h9012
                              · rcases h4bigk with h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h7647, hlam, p9013_1]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h7647, h8383, h8386, h8901, hc12, hlam, hphi, ht01, ht0b, ht5b, p9013_1, u5ehi4]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h7647, h8383, h8386, h8899, h8902, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8954_1, p9013_1]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  rcases p9013_3 (m.d 0 4) (by simp) with h9018 | h9018
                                  · rcases p9013_3 (m.d 1 4) (by simp) with h9019 | h9019
                                    · rcases p9013_3 (m.d 2 4) (by simp) with h9020 | h9020
                                      · linarith only [h8379, h9020, hlam]
                                      · linarith only [h8901, h9020, hlam]
                                    · linarith only [h8388, h9019, hlam]
                                  · linarith only [h9018, hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8379, h8383, h8386, h8901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8954_1, p9013_1]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8383, h8386, h8901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8954_1, p9013_1]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8383, h8386, h8899, h8902, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8954_1, p9013_1]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  rcases p9013_3 (m.d 0 4) (by simp) with h9029 | h9029
                                  · linarith only [h7647, h9029, hlam]
                                  · linarith only [h8382, h9029, hlam]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8379, hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8384, hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8389, hlam, p9013_1]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h0, h8379, hc12, hlam, hphi, ht01, ht0b, ht5b, p9013_1, u5ehi4]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8381, hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8386, hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8381, h8901, hc04, hlam, hphi, ht0b, ht5b, p9013_1, u5ehi4]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h0, h8378, h8381, hc12, hlam, hphi, ht01, ht0b, ht5b, p9013_1, u5ehi4]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8382, hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8388, hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8901, hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [h8902, hlam, p9013_0]
                                · have p9013_0 := h9013c.1
                                  have p9013_1 := h9013c.2.1
                                  have p9013_2 := h9013c.2.2.1
                                  have p9013_3 := h9013c.2.2.2
                                  linarith only [hlam, p9013_0]
                              · linarith only [h8899, h9012, hlam]
                            · linarith only [h8389, h9011, hlam]
                        · linarith only [h8383, h9008, hlam]
                      · linarith only [h8378, h9007, hlam]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [h8901, hlam, p8954_1]
                    · have p8954_0 := h8954c.1
                      have p8954_1 := h8954c.2.1
                      have p8954_2 := h8954c.2.2.1
                      have p8954_3 := h8954c.2.2.2
                      linarith only [hlam, p8954_0]
                  · linarith only [h8953, hlam, p8903_0]
                · linarith only [h7647, h8952, hlam]
              · linarith only [h6794, h8951, hlam]
            · linarith only [h0, h8950, hlam]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h8385, hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h8387, hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [h8388, hlam, p8903_0]
        · have p8903_0 := h8903c.1
          have p8903_1 := h8903c.2.1
          have p8903_2 := h8903c.2.2.1
          have p8903_3 := h8903c.2.2.2
          linarith only [hlam, p8903_0]
      · linarith only [h8389, h8901, h8902, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h9062 | h9062
      · rcases h1bigk with h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c | h9063c
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h0, hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h6794, hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h7647, hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h8170, hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          rcases p9063_3 (m.d 0 1) (by simp) with h9069 | h9069
          · linarith only [h9069, hlam, p9063_0]
          · rcases p9063_3 (m.d 1 2) (by simp) with h9071 | h9071
            · rcases p9063_3 (m.d 1 3) (by simp) with h9072 | h9072
              · linarith only [h8383, h9072, hlam]
              · linarith only [h6794, h9072, hlam]
            · linarith only [h9071, hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h6794, hc01, hc12, hlam, hphi, p9063_1]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h7647, h8381, h8389, h8901, h9062, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9063_1]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h8170, hc01, hc12, hlam, hphi, p9063_1]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          rcases p9063_3 (m.d 0 1) (by simp) with h9080 | h9080
          · linarith only [h9080, hlam, p9063_0]
          · rcases p9063_3 (m.d 1 2) (by simp) with h9082 | h9082
            · rcases p9063_3 (m.d 1 3) (by simp) with h9083 | h9083
              · rcases p9063_3 (m.d 1 4) (by simp) with h9084 | h9084
                · linarith only [h8386, h9084, hlam]
                · linarith only [h7647, h9084, hlam]
              · linarith only [h9083, hlam, p9063_0]
            · linarith only [h0, h9082, hlam]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h8383, hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h7647, h8381, h8389, h8901, h9062, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9063_1]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h8170, h8383, hc01, hc12, hlam, hphi, p9063_1]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          rcases p9063_3 (m.d 0 1) (by simp) with h9093 | h9093
          · linarith only [h9093, hlam, p9063_0]
          · rcases p9063_3 (m.d 1 2) (by simp) with h9095 | h9095
            · rcases p9063_3 (m.d 1 3) (by simp) with h9096 | h9096
              · rcases p9063_3 (m.d 1 4) (by simp) with h9097 | h9097
                · rcases p9063_3 (m.d 1 5) (by simp) with h9098 | h9098
                  · linarith only [h8388, h9098, hlam]
                  · linarith only [h8170, h9098, hlam]
                · linarith only [h9097, hlam, p9063_0]
              · linarith only [h6794, h9096, hlam]
            · linarith only [h0, h9095, hlam]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h8384, hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h8386, hlam, p9063_1]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h8170, hc01, hc14, hlam, hphi, p9063_1]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          rcases p9063_3 (m.d 0 1) (by simp) with h9108 | h9108
          · linarith only [h9108, hlam, p9063_0]
          · rcases p9063_3 (m.d 1 2) (by simp) with h9110 | h9110
            · rcases p9063_3 (m.d 1 3) (by simp) with h9111 | h9111
              · rcases p9063_3 (m.d 1 4) (by simp) with h9112 | h9112
                · rcases p9063_3 (m.d 1 5) (by simp) with h9113 | h9113
                  · rcases h2bigk with h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c | h9114c
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h0, hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8378, h8381, h8389, h8901, h9062, hlam, p9114_2]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8378, h8381, h8901, h9062, hlam, p9114_2]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      rcases p9114_3 (m.d 0 2) (by simp) with h9119 | h9119
                      · rcases p9114_3 (m.d 1 2) (by simp) with h9120 | h9120
                        · rcases p9114_3 (m.d 2 3) (by simp) with h9121 | h9121
                          · linarith only [h8378, h9121, hlam]
                          · rcases p9114_3 (m.d 2 4) (by simp) with h9123 | h9123
                            · linarith only [h8379, h9123, hlam]
                            · rcases p9114_3 (m.d 2 5) (by simp) with h9125 | h9125
                              · linarith only [h9125, hlam, p9114_0]
                              · rcases h4bigk with h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c | h9127c
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h7647, hlam, p9127_1]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  rcases p9127_3 (m.d 0 4) (by simp) with h9130 | h9130
                                  · rcases p9127_3 (m.d 1 4) (by simp) with h9131 | h9131
                                    · rcases p9127_3 (m.d 2 4) (by simp) with h9132 | h9132
                                      · linarith only [h8379, h9132, hlam]
                                      · rcases p9127_3 (m.d 3 4) (by simp) with h9134 | h9134
                                        · linarith only [h8381, h9134, hlam]
                                        · linarith only [h8389, h9134, hlam]
                                    · linarith only [h8384, h9131, hlam]
                                  · linarith only [h8379, h9130, hlam]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8389, h8901, h9062, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9127_1]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  rcases p9127_3 (m.d 0 4) (by simp) with h9140 | h9140
                                  · rcases p9127_3 (m.d 1 4) (by simp) with h9141 | h9141
                                    · rcases p9127_3 (m.d 2 4) (by simp) with h9142 | h9142
                                      · linarith only [h8379, h9142, hlam]
                                      · rcases p9127_3 (m.d 3 4) (by simp) with h9144 | h9144
                                        · linarith only [h8381, h9144, hlam]
                                        · linarith only [h9062, h9144, hlam]
                                    · linarith only [h8388, h9141, hlam]
                                  · linarith only [h9140, hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8381, h8383, h8386, h8389, h8901, h9062, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9127_1]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  rcases p9127_3 (m.d 0 4) (by simp) with h9151 | h9151
                                  · linarith only [h7647, h9151, hlam]
                                  · linarith only [h8379, h9151, hlam]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8389, h8901, h9062, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9127_1]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  rcases p9127_3 (m.d 0 4) (by simp) with h9155 | h9155
                                  · linarith only [h7647, h9155, hlam]
                                  · linarith only [h8382, h9155, hlam]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8379, hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8384, hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8389, hlam, p9127_1]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8901, hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8381, hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8386, hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  rcases p9127_3 (m.d 0 4) (by simp) with h9165 | h9165
                                  · rcases p9127_3 (m.d 1 4) (by simp) with h9166 | h9166
                                    · rcases p9127_3 (m.d 2 4) (by simp) with h9167 | h9167
                                      · linarith only [h8389, h9167, hlam]
                                      · rcases p9127_3 (m.d 3 4) (by simp) with h9169 | h9169
                                        · rcases p9127_3 (m.d 4 5) (by simp) with h9170 | h9170
                                          · linarith only [h9062, h9170, hlam]
                                          · linarith only [h8901, h9170, hlam]
                                        · linarith only [h8389, h9169, hlam]
                                    · linarith only [h8384, h9166, hlam]
                                  · linarith only [h8379, h9165, hlam]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8378, h8381, h8389, h8901, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9127_1]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8382, hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h8388, hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h0, h8378, h8381, h8389, h9062, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9127_1]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [h9062, hlam, p9127_0]
                                · have p9127_0 := h9127c.1
                                  have p9127_1 := h9127c.2.1
                                  have p9127_2 := h9127c.2.2.1
                                  have p9127_3 := h9127c.2.2.2
                                  linarith only [hlam, p9127_0]
                        · linarith only [h8385, h9120, hlam]
                      · linarith only [h9119, hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8379, h8382, hc12, hlam, hphi, ht01, ht0b, ht5b, p9114_1, u5ehi4]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h0, h8378, h8381, h8389, h8901, h9062, hlam, p9114_2]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h0, h8378, h8381, h8901, h9062, hlam, p9114_2]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      rcases p9114_3 (m.d 0 2) (by simp) with h9189 | h9189
                      · linarith only [h0, h9189, hlam]
                      · linarith only [h8380, h9189, hlam]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8378, hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8383, hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8389, hlam, p9114_1]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8899, hlam, p9114_1]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8379, hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8384, hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h0, h8378, h8381, h8901, h9062, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9114_1]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8901, hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8380, hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h8385, hlam, p9114_0]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h0, h8378, h8381, h8901, h9062, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9114_1]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [h0, h8378, h8381, h8901, h9062, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9114_1]
                    · have p9114_0 := h9114c.1
                      have p9114_1 := h9114c.2.1
                      have p9114_2 := h9114c.2.2.1
                      have p9114_3 := h9114c.2.2.2
                      linarith only [hlam, p9114_0]
                  · linarith only [h9113, hlam, p9063_0]
                · linarith only [h7647, h9112, hlam]
              · linarith only [h6794, h9111, hlam]
            · linarith only [h0, h9110, hlam]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h8385, hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h8387, hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [h8388, hlam, p9063_0]
        · have p9063_0 := h9063c.1
          have p9063_1 := h9063c.2.1
          have p9063_2 := h9063c.2.2.1
          have p9063_3 := h9063c.2.2.2
          linarith only [hlam, p9063_0]
      · rcases h1bigk with h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c | h9215c
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h0, hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h6794, hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h7647, hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h8170, hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          rcases p9215_3 (m.d 0 1) (by simp) with h9221 | h9221
          · linarith only [h9221, hlam, p9215_0]
          · rcases p9215_3 (m.d 1 2) (by simp) with h9223 | h9223
            · rcases p9215_3 (m.d 1 3) (by simp) with h9224 | h9224
              · linarith only [h8383, h9224, hlam]
              · linarith only [h6794, h9224, hlam]
            · linarith only [h9223, hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h7647, h8382, h8386, h9062, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9215_1]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h7647, h8382, h9062, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9215_1]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h8170, hc01, hc12, hlam, hphi, p9215_1]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          rcases p9215_3 (m.d 0 1) (by simp) with h9232 | h9232
          · linarith only [h9232, hlam, p9215_0]
          · rcases p9215_3 (m.d 1 2) (by simp) with h9234 | h9234
            · rcases p9215_3 (m.d 1 3) (by simp) with h9235 | h9235
              · rcases p9215_3 (m.d 1 4) (by simp) with h9236 | h9236
                · linarith only [h8386, h9236, hlam]
                · linarith only [h7647, h9236, hlam]
              · linarith only [h9235, hlam, p9215_0]
            · linarith only [h0, h9234, hlam]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h8383, hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h7647, h8382, h8389, h9062, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9215_1]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h8170, h8382, h8383, h8389, h9062, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9215_1]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          rcases p9215_3 (m.d 0 1) (by simp) with h9245 | h9245
          · linarith only [h9245, hlam, p9215_0]
          · rcases p9215_3 (m.d 1 2) (by simp) with h9247 | h9247
            · rcases p9215_3 (m.d 1 3) (by simp) with h9248 | h9248
              · rcases p9215_3 (m.d 1 4) (by simp) with h9249 | h9249
                · rcases p9215_3 (m.d 1 5) (by simp) with h9250 | h9250
                  · linarith only [h8388, h9250, hlam]
                  · linarith only [h8170, h9250, hlam]
                · linarith only [h9249, hlam, p9215_0]
              · linarith only [h6794, h9248, hlam]
            · linarith only [h0, h9247, hlam]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h8384, hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h8386, hlam, p9215_1]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h8170, h8382, h8389, h9062, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9215_1]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          rcases p9215_3 (m.d 0 1) (by simp) with h9260 | h9260
          · linarith only [h9260, hlam, p9215_0]
          · rcases p9215_3 (m.d 1 2) (by simp) with h9262 | h9262
            · rcases p9215_3 (m.d 1 3) (by simp) with h9263 | h9263
              · rcases p9215_3 (m.d 1 4) (by simp) with h9264 | h9264
                · rcases p9215_3 (m.d 1 5) (by simp) with h9265 | h9265
                  · rcases h2bigk with h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h0, hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h8378, h8381, h8382, h8389, h9062, hlam, p9266_2]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      rcases p9266_3 (m.d 0 2) (by simp) with h9270 | h9270
                      · rcases p9266_3 (m.d 1 2) (by simp) with h9271 | h9271
                        · rcases p9266_3 (m.d 2 3) (by simp) with h9272 | h9272
                          · linarith only [h8378, h9272, hlam]
                          · rcases p9266_3 (m.d 2 4) (by simp) with h9274 | h9274
                            · linarith only [h9274, hlam, p9266_0]
                            · rcases p9266_3 (m.d 2 5) (by simp) with h9276 | h9276
                              · linarith only [h8380, h9276, hlam]
                              · linarith only [h8901, h9276, hlam]
                        · linarith only [h8384, h9271, hlam]
                      · linarith only [h9270, hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      rcases p9266_3 (m.d 0 2) (by simp) with h9281 | h9281
                      · rcases p9266_3 (m.d 1 2) (by simp) with h9282 | h9282
                        · rcases p9266_3 (m.d 2 3) (by simp) with h9283 | h9283
                          · linarith only [h8378, h9283, hlam]
                          · rcases p9266_3 (m.d 2 4) (by simp) with h9285 | h9285
                            · linarith only [h8379, h9285, hlam]
                            · rcases p9266_3 (m.d 2 5) (by simp) with h9287 | h9287
                              · linarith only [h9287, hlam, p9266_0]
                              · rcases h4bigk with h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c | h9289c
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h7647, hlam, p9289_1]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  rcases p9289_3 (m.d 0 4) (by simp) with h9292 | h9292
                                  · rcases p9289_3 (m.d 1 4) (by simp) with h9293 | h9293
                                    · rcases p9289_3 (m.d 2 4) (by simp) with h9294 | h9294
                                      · linarith only [h8379, h9294, hlam]
                                      · rcases p9289_3 (m.d 3 4) (by simp) with h9296 | h9296
                                        · linarith only [h8381, h9296, hlam]
                                        · linarith only [h8389, h9296, hlam]
                                    · linarith only [h8384, h9293, hlam]
                                  · linarith only [h8379, h9292, hlam]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  rcases p9289_3 (m.d 0 4) (by simp) with h9301 | h9301
                                  · rcases p9289_3 (m.d 1 4) (by simp) with h9302 | h9302
                                    · rcases p9289_3 (m.d 2 4) (by simp) with h9303 | h9303
                                      · linarith only [h8379, h9303, hlam]
                                      · rcases p9289_3 (m.d 3 4) (by simp) with h9305 | h9305
                                        · linarith only [h8381, h9305, hlam]
                                        · rcases p9289_3 (m.d 4 5) (by simp) with h9307 | h9307
                                          · linarith only [h8382, h9307, hlam]
                                          · linarith only [h9062, h9307, hlam]
                                    · linarith only [h8386, h9302, hlam]
                                  · linarith only [h8381, h9301, hlam]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8378, h8381, h8389, h9062, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9289_1]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8382, h8383, h8386, h8389, h9062, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9289_1]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  rcases p9289_3 (m.d 0 4) (by simp) with h9315 | h9315
                                  · linarith only [h7647, h9315, hlam]
                                  · linarith only [h8379, h9315, hlam]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  rcases p9289_3 (m.d 0 4) (by simp) with h9318 | h9318
                                  · linarith only [h7647, h9318, hlam]
                                  · linarith only [h8381, h9318, hlam]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8383, h8386, h8389, h9062, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9289_1]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8379, hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8384, hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8389, hlam, p9289_1]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8901, hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8381, hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8386, hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8382, h9062, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p9289_1]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h9062, hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8382, hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h8388, hlam, p9289_0]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  rcases p9289_3 (m.d 0 4) (by simp) with h9334 | h9334
                                  · rcases p9289_3 (m.d 1 4) (by simp) with h9335 | h9335
                                    · rcases p9289_3 (m.d 2 4) (by simp) with h9336 | h9336
                                      · linarith only [h9336, hlam, p9289_0]
                                      · rcases p9289_3 (m.d 3 4) (by simp) with h9338 | h9338
                                        · linarith only [h9062, h9338, hlam]
                                        · linarith only [h8389, h9338, hlam]
                                    · linarith only [h8384, h9335, hlam]
                                  · linarith only [h8379, h9334, hlam]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [h7647, h8382, h8383, h8386, h8389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9289_1]
                                · have p9289_0 := h9289c.1
                                  have p9289_1 := h9289c.2.1
                                  have p9289_2 := h9289c.2.2.1
                                  have p9289_3 := h9289c.2.2.2
                                  linarith only [hlam, p9289_0]
                        · linarith only [h8385, h9282, hlam]
                      · linarith only [h9281, hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h8379, h8382, hc12, hlam, hphi, ht01, ht0b, ht5b, p9266_1, u5ehi4]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h0, h8378, h8381, h8382, h8389, h9062, hlam, p9266_2]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      rcases p9266_3 (m.d 0 2) (by simp) with h9350 | h9350
                      · linarith only [h0, h9350, hlam]
                      · linarith only [h8379, h9350, hlam]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      rcases p9266_3 (m.d 0 2) (by simp) with h9353 | h9353
                      · linarith only [h0, h9353, hlam]
                      · linarith only [h8380, h9353, hlam]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h8378, hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h8383, hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h8389, hlam, p9266_1]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h8899, hlam, p9266_1]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h8379, hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h8384, hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h0, h8378, h8381, h8382, h8389, h9062, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9266_1]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h8901, hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h8380, hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [h8385, hlam, p9266_0]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      rcases p9266_3 (m.d 0 2) (by simp) with h9368 | h9368
                      · rcases p9266_3 (m.d 1 2) (by simp) with h9369 | h9369
                        · rcases p9266_3 (m.d 2 3) (by simp) with h9370 | h9370
                          · linarith only [h8899, h9370, hlam]
                          · rcases p9266_3 (m.d 2 4) (by simp) with h9372 | h9372
                            · linarith only [h8901, h9372, hlam]
                            · linarith only [h8389, h9372, hlam]
                        · linarith only [h8383, h9369, hlam]
                      · linarith only [h8378, h9368, hlam]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      rcases p9266_3 (m.d 0 2) (by simp) with h9377 | h9377
                      · rcases p9266_3 (m.d 1 2) (by simp) with h9378 | h9378
                        · rcases p9266_3 (m.d 2 3) (by simp) with h9379 | h9379
                          · linarith only [h8899, h9379, hlam]
                          · rcases p9266_3 (m.d 2 4) (by simp) with h9381 | h9381
                            · linarith only [h8901, h9381, hlam]
                            · rcases p9266_3 (m.d 2 5) (by simp) with h9383 | h9383
                              · rcases h4bigk with h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h7647, hlam, p9384_1]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8382, h8901, hlam, p9266_1, p9384_2]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  rcases p9384_3 (m.d 0 4) (by simp) with h9388 | h9388
                                  · rcases p9384_3 (m.d 1 4) (by simp) with h9389 | h9389
                                    · rcases p9384_3 (m.d 2 4) (by simp) with h9390 | h9390
                                      · linarith only [h8379, h9390, hlam]
                                      · rcases p9384_3 (m.d 3 4) (by simp) with h9392 | h9392
                                        · linarith only [h8381, h9392, hlam]
                                        · rcases p9384_3 (m.d 4 5) (by simp) with h9394 | h9394
                                          · linarith only [h8382, h9394, hlam]
                                          · linarith only [h9062, h9394, hlam]
                                    · linarith only [h8386, h9389, hlam]
                                  · linarith only [h8381, h9388, hlam]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h0, h8378, h8381, h8899, h9062, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9266_1, p9384_1]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8382, h8383, h8386, h8899, h9062, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9266_1, p9384_1]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h7647, h8382, h8899, h9062, hlam, p9266_1, p9384_2]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  rcases p9384_3 (m.d 0 4) (by simp) with h9403 | h9403
                                  · linarith only [h7647, h9403, hlam]
                                  · linarith only [h8381, h9403, hlam]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8389, h8899, h9062, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9266_1, p9384_1]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8379, hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8384, hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8389, hlam, p9384_1]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8901, hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8381, hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8386, hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8382, h8389, h9062, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9384_1]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h9062, hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8382, hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h8388, hlam, p9384_0]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  rcases p9384_3 (m.d 0 4) (by simp) with h9419 | h9419
                                  · rcases p9384_3 (m.d 1 4) (by simp) with h9420 | h9420
                                    · rcases p9384_3 (m.d 2 4) (by simp) with h9421 | h9421
                                      · linarith only [h9421, hlam, p9384_0]
                                      · rcases p9384_3 (m.d 3 4) (by simp) with h9423 | h9423
                                        · linarith only [h9062, h9423, hlam]
                                        · linarith only [h8389, h9423, hlam]
                                    · linarith only [h8384, h9420, hlam]
                                  · linarith only [h8379, h9419, hlam]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [h7647, h8382, h8383, h8386, h8389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9384_1]
                                · have p9384_0 := h9384c.1
                                  have p9384_1 := h9384c.2.1
                                  have p9384_2 := h9384c.2.2.1
                                  have p9384_3 := h9384c.2.2.2
                                  linarith only [hlam, p9384_0]
                              · linarith only [h8901, h9383, hlam]
                        · linarith only [h8384, h9378, hlam]
                      · linarith only [h8379, h9377, hlam]
                    · have p9266_0 := h9266c.1
                      have p9266_1 := h9266c.2.1
                      have p9266_2 := h9266c.2.2.1
                      have p9266_3 := h9266c.2.2.2
                      linarith only [hlam, p9266_0]
                  · linarith only [h9265, hlam, p9215_0]
                · linarith only [h7647, h9264, hlam]
              · linarith only [h6794, h9263, hlam]
            · linarith only [h0, h9262, hlam]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h8385, hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h8387, hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [h8388, hlam, p9215_0]
        · have p9215_0 := h9215c.1
          have p9215_1 := h9215c.2.1
          have p9215_2 := h9215c.2.2.1
          have p9215_3 := h9215c.2.2.2
          linarith only [hlam, p9215_0]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8385 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8386 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h8387 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h8388 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 2 3 4 (by decide) (by decide) with h8389 | h8389
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384 h8385 h8386 h8387 h8388 h8389
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384 h8385 h8386 h8387 h8388 h8389

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8385 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8386 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h8387 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h8388 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  linarith only [h7647, h8382, h8388, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8385 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8386 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h8387 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 1 4 5 (by decide) (by decide) with h8388 | h8388
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384 h8385 h8386 h8387 h8388
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384 h8385 h8386 h8387 h8388

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8385 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8386 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h8387 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 1 4 5 (by decide) (by decide) with h9443 | h9443
  · linarith only [h8386, h8387, h9443, hlam]
  · linarith only [h7647, h8382, h9443, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8385 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8386 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 1 3 5 (by decide) (by decide) with h8387 | h8387
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384 h8385 h8386 h8387
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384 h8385 h8386 h8387

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8385 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8386 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  linarith only [h6794, h8381, h8386, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8385 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 1 3 4 (by decide) (by decide) with h8386 | h8386
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384 h8385 h8386
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384 h8385 h8386

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8385 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  linarith only [h0, h8380, h8385, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 1 2 5 (by decide) (by decide) with h8385 | h8385
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384 h8385
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384 h8385

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  linarith only [h0, h8379, h8384, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 1 2 4 (by decide) (by decide) with h8384 | h8384
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381 h8382 h8383 h8384

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  linarith only [h0, h8378, h8383, hlam]

end R2N4
