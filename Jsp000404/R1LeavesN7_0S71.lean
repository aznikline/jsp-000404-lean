import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h41040 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  rcases m.htr 2 4 5 (by decide) (by decide) with h41041 | h41041
  · rcases m.htr 3 4 5 (by decide) (by decide) with h41042 | h41042
    · rcases h1bigk with h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c | h41043c
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h0, hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h33187, hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h36828, hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h39227, hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        rcases p41043_3 (m.d 0 1) (by simp) with h41049 | h41049
        · linarith only [h41049, hlam, p41043_0]
        · rcases p41043_3 (m.d 1 2) (by simp) with h41051 | h41051
          · rcases p41043_3 (m.d 1 3) (by simp) with h41052 | h41052
            · linarith only [h41033, h41052, hlam]
            · linarith only [h33187, h41052, hlam]
          · linarith only [h41051, hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h33187, hc01, hc12, hlam, hphi, p41043_1]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h36828, hc01, hc12, hlam, hphi, p41043_1]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h39227, hc01, hc12, hlam, hphi, p41043_1]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        rcases p41043_3 (m.d 0 1) (by simp) with h41060 | h41060
        · linarith only [h41060, hlam, p41043_0]
        · rcases p41043_3 (m.d 1 2) (by simp) with h41062 | h41062
          · rcases p41043_3 (m.d 1 3) (by simp) with h41063 | h41063
            · rcases p41043_3 (m.d 1 4) (by simp) with h41064 | h41064
              · linarith only [h41036, h41064, hlam]
              · linarith only [h36828, h41064, hlam]
            · linarith only [h41063, hlam, p41043_0]
          · linarith only [h0, h41062, hlam]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h41033, hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h39227, h41038, hc01, hc13, hlam, hphi, p41043_1]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h39227, h41033, hc01, hc12, hlam, hphi, p41043_1]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        rcases p41043_3 (m.d 0 1) (by simp) with h41073 | h41073
        · linarith only [h41073, hlam, p41043_0]
        · rcases p41043_3 (m.d 1 2) (by simp) with h41075 | h41075
          · rcases p41043_3 (m.d 1 3) (by simp) with h41076 | h41076
            · rcases p41043_3 (m.d 1 4) (by simp) with h41077 | h41077
              · rcases p41043_3 (m.d 1 5) (by simp) with h41078 | h41078
                · linarith only [h41038, h41078, hlam]
                · linarith only [h39227, h41078, hlam]
              · linarith only [h41077, hlam, p41043_0]
            · linarith only [h33187, h41076, hlam]
          · linarith only [h0, h41075, hlam]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h41034, hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h41036, hlam, p41043_1]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h39227, hc01, hc14, hlam, hphi, p41043_1]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        rcases p41043_3 (m.d 0 1) (by simp) with h41088 | h41088
        · linarith only [h41088, hlam, p41043_0]
        · rcases p41043_3 (m.d 1 2) (by simp) with h41090 | h41090
          · rcases p41043_3 (m.d 1 3) (by simp) with h41091 | h41091
            · rcases p41043_3 (m.d 1 4) (by simp) with h41092 | h41092
              · rcases p41043_3 (m.d 1 5) (by simp) with h41093 | h41093
                · rcases h1emax with h41094 | h41094 | h41094 | h41094 | h41094
                  · rcases h2bigk with h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c | h41095c
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h0, hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h0, h41039, h41042, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p41095_1]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      rcases p41095_3 (m.d 0 2) (by simp) with h41099 | h41099
                      · rcases p41095_3 (m.d 1 2) (by simp) with h41100 | h41100
                        · rcases p41095_3 (m.d 2 3) (by simp) with h41101 | h41101
                          · linarith only [h41027, h41101, hlam]
                          · linarith only [h41039, h41101, hlam]
                        · linarith only [h41034, h41100, hlam]
                      · linarith only [h41099, hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      rcases p41095_3 (m.d 0 2) (by simp) with h41106 | h41106
                      · rcases p41095_3 (m.d 1 2) (by simp) with h41107 | h41107
                        · rcases p41095_3 (m.d 2 3) (by simp) with h41108 | h41108
                          · linarith only [h41027, h41108, hlam]
                          · linarith only [h41040, h41108, hlam]
                        · linarith only [h41035, h41107, hlam]
                      · linarith only [h41106, hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41027, h41039, h41042, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p41095_1]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41039, h41042, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p41095_1]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      rcases p41095_3 (m.d 0 2) (by simp) with h41116 | h41116
                      · linarith only [h0, h41116, hlam]
                      · linarith only [h41028, h41116, hlam]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      rcases p41095_3 (m.d 0 2) (by simp) with h41119 | h41119
                      · linarith only [h0, h41119, hlam]
                      · linarith only [h41029, h41119, hlam]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41027, hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41033, hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41027, h41039, h41042, hc02, hc45, hlam, hphi, ht0b, ht5b, p41095_1]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      rcases p41095_3 (m.d 0 2) (by simp) with h41126 | h41126
                      · rcases p41095_3 (m.d 1 2) (by simp) with h41127 | h41127
                        · rcases p41095_3 (m.d 2 3) (by simp) with h41128 | h41128
                          · rcases p41095_3 (m.d 2 4) (by simp) with h41129 | h41129
                            · linarith only [h41039, h41129, hlam]
                            · linarith only [h41041, h41129, hlam]
                          · linarith only [h41040, h41128, hlam]
                        · linarith only [h41035, h41127, hlam]
                      · linarith only [h41029, h41126, hlam]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41028, hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41034, hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41039, hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      rcases p41095_3 (m.d 0 2) (by simp) with h41139 | h41139
                      · rcases p41095_3 (m.d 1 2) (by simp) with h41140 | h41140
                        · rcases p41095_3 (m.d 2 3) (by simp) with h41141 | h41141
                          · rcases p41095_3 (m.d 2 4) (by simp) with h41142 | h41142
                            · rcases p41095_3 (m.d 2 5) (by simp) with h41143 | h41143
                              · linarith only [h41041, h41143, hlam]
                              · rcases h4bigk with h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c | h41145c
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h36828, hlam, p41145_1]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h33187, h41030, h41033, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p41095_1, p41145_1]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  rcases p41145_3 (m.d 0 4) (by simp) with h41149 | h41149
                                  · rcases p41145_3 (m.d 1 4) (by simp) with h41150 | h41150
                                    · rcases p41145_3 (m.d 2 4) (by simp) with h41151 | h41151
                                      · linarith only [h41028, h41151, hlam]
                                      · linarith only [h41039, h41151, hlam]
                                    · linarith only [h41036, h41150, hlam]
                                  · linarith only [h41030, h41149, hlam]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  rcases p41145_3 (m.d 0 4) (by simp) with h41156 | h41156
                                  · rcases p41145_3 (m.d 1 4) (by simp) with h41157 | h41157
                                    · rcases p41145_3 (m.d 2 4) (by simp) with h41158 | h41158
                                      · linarith only [h41028, h41158, hlam]
                                      · linarith only [h41041, h41158, hlam]
                                    · linarith only [h41038, h41157, hlam]
                                  · linarith only [h41156, hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h41028, h41033, h41036, h41040, h41042, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p41095_1, p41145_1]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h41033, h41036, h41040, h41042, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p41095_1, p41145_1]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  rcases p41145_3 (m.d 0 4) (by simp) with h41166 | h41166
                                  · linarith only [h36828, h41166, hlam]
                                  · linarith only [h41030, h41166, hlam]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  rcases p41145_3 (m.d 0 4) (by simp) with h41169 | h41169
                                  · linarith only [h36828, h41169, hlam]
                                  · linarith only [h41032, h41169, hlam]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h41028, hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h41034, hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h0, h41028, h41042, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p41145_1]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  rcases p41145_3 (m.d 0 4) (by simp) with h41176 | h41176
                                  · rcases p41145_3 (m.d 1 4) (by simp) with h41177 | h41177
                                    · rcases p41145_3 (m.d 2 4) (by simp) with h41178 | h41178
                                      · rcases p41145_3 (m.d 3 4) (by simp) with h41179 | h41179
                                        · linarith only [h41039, h41179, hlam]
                                        · linarith only [h41042, h41179, hlam]
                                      · linarith only [h41178, hlam, p41145_0]
                                    · linarith only [h41038, h41177, hlam]
                                  · linarith only [h41032, h41176, hlam]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h41030, hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h41036, hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h41039, hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h0, h41027, h41039, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p41145_1]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h41032, hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h41038, hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h41041, hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [h41042, hlam, p41145_0]
                                · have p41145_0 := h41145c.1
                                  have p41145_1 := h41145c.2.1
                                  have p41145_2 := h41145c.2.2.1
                                  have p41145_3 := h41145c.2.2.2
                                  linarith only [hlam, p41145_0]
                            · linarith only [h41041, h41142, hlam]
                          · linarith only [h41040, h41141, hlam]
                        · linarith only [h41035, h41140, hlam]
                      · linarith only [h41029, h41139, hlam]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41029, hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41035, hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41040, hlam, p41095_0]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [h41041, hlam, p41095_1]
                    · have p41095_0 := h41095c.1
                      have p41095_1 := h41095c.2.1
                      have p41095_2 := h41095c.2.2.1
                      have p41095_3 := h41095c.2.2.2
                      linarith only [hlam, p41095_0]
                  · linarith only [h0, h41027, h41039, h41094, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h41036, h41038, h41094, hc01, hlam, p41043_1]
                  · linarith only [h41038, h41094, hc01, hlam, p41043_1]
                  · linarith only [h41094, hc01, hlam, p41043_1]
                · linarith only [h41093, hlam, p41043_0]
              · linarith only [h36828, h41092, hlam]
            · linarith only [h33187, h41091, hlam]
          · linarith only [h0, h41090, hlam]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h41035, hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h41037, hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [h41038, hlam, p41043_0]
      · have p41043_0 := h41043c.1
        have p41043_1 := h41043c.2.1
        have p41043_2 := h41043c.2.2.1
        have p41043_3 := h41043c.2.2.2
        linarith only [hlam, p41043_0]
    · rcases h1bigk with h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c | h41216c
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h0, hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h33187, hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h36828, hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h39227, hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        rcases p41216_3 (m.d 0 1) (by simp) with h41222 | h41222
        · linarith only [h41222, hlam, p41216_0]
        · rcases p41216_3 (m.d 1 2) (by simp) with h41224 | h41224
          · rcases p41216_3 (m.d 1 3) (by simp) with h41225 | h41225
            · linarith only [h41033, h41225, hlam]
            · linarith only [h33187, h41225, hlam]
          · linarith only [h41224, hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h33187, hc01, hc12, hlam, hphi, p41216_1]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h36828, h41032, h41042, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41216_1]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h39227, hc01, hc12, hlam, hphi, p41216_1]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        rcases p41216_3 (m.d 0 1) (by simp) with h41233 | h41233
        · linarith only [h41233, hlam, p41216_0]
        · rcases p41216_3 (m.d 1 2) (by simp) with h41235 | h41235
          · rcases p41216_3 (m.d 1 3) (by simp) with h41236 | h41236
            · rcases p41216_3 (m.d 1 4) (by simp) with h41237 | h41237
              · linarith only [h41036, h41237, hlam]
              · linarith only [h36828, h41237, hlam]
            · linarith only [h41236, hlam, p41216_0]
          · linarith only [h0, h41235, hlam]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h41033, hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h36828, h41028, h41041, h41042, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41216_1]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h39227, h41033, hc01, hc12, hlam, hphi, p41216_1]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        rcases p41216_3 (m.d 0 1) (by simp) with h41246 | h41246
        · linarith only [h41246, hlam, p41216_0]
        · rcases p41216_3 (m.d 1 2) (by simp) with h41248 | h41248
          · rcases p41216_3 (m.d 1 3) (by simp) with h41249 | h41249
            · rcases p41216_3 (m.d 1 4) (by simp) with h41250 | h41250
              · rcases p41216_3 (m.d 1 5) (by simp) with h41251 | h41251
                · linarith only [h41038, h41251, hlam]
                · linarith only [h39227, h41251, hlam]
              · linarith only [h41250, hlam, p41216_0]
            · linarith only [h33187, h41249, hlam]
          · linarith only [h0, h41248, hlam]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h41034, hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h41036, hlam, p41216_1]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h39227, hc01, hc14, hlam, hphi, p41216_1]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        rcases p41216_3 (m.d 0 1) (by simp) with h41261 | h41261
        · linarith only [h41261, hlam, p41216_0]
        · rcases p41216_3 (m.d 1 2) (by simp) with h41263 | h41263
          · rcases p41216_3 (m.d 1 3) (by simp) with h41264 | h41264
            · rcases p41216_3 (m.d 1 4) (by simp) with h41265 | h41265
              · rcases p41216_3 (m.d 1 5) (by simp) with h41266 | h41266
                · rcases h1emax with h41267 | h41267 | h41267 | h41267 | h41267
                  · rcases h2bigk with h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c | h41268c
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h0, hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h0, h41039, h41041, h41042, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41268_1]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h0, h41041, h41042, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41268_1]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      rcases p41268_3 (m.d 0 2) (by simp) with h41273 | h41273
                      · rcases p41268_3 (m.d 1 2) (by simp) with h41274 | h41274
                        · rcases p41268_3 (m.d 2 3) (by simp) with h41275 | h41275
                          · linarith only [h41027, h41275, hlam]
                          · linarith only [h41040, h41275, hlam]
                        · linarith only [h41035, h41274, hlam]
                      · linarith only [h41273, hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41027, h41039, h41041, h41042, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41268_1]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41039, h41041, h41042, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41268_1]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41041, h41042, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41268_1]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      rcases p41268_3 (m.d 0 2) (by simp) with h41284 | h41284
                      · linarith only [h0, h41284, hlam]
                      · linarith only [h41029, h41284, hlam]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41027, hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41033, hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41027, h41041, h41042, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p41268_1]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h0, h41027, h41041, h41042, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41268_1]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41028, hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41034, hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41039, hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h0, h41028, h41041, h41042, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41268_1]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41029, hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41035, hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41040, hlam, p41268_0]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [h41041, hlam, p41268_1]
                    · have p41268_0 := h41268c.1
                      have p41268_1 := h41268c.2.1
                      have p41268_2 := h41268c.2.2.1
                      have p41268_3 := h41268c.2.2.2
                      linarith only [hlam, p41268_0]
                  · linarith only [h0, h41267, hc01, hlam]
                  · linarith only [h41036, h41038, h41267, hc01, hlam, p41216_1]
                  · linarith only [h41038, h41267, hc01, hlam, p41216_1]
                  · linarith only [h41267, hc01, hlam, p41216_1]
                · linarith only [h41266, hlam, p41216_0]
              · linarith only [h36828, h41265, hlam]
            · linarith only [h33187, h41264, hlam]
          · linarith only [h0, h41263, hlam]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h41035, hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h41037, hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [h41038, hlam, p41216_0]
      · have p41216_0 := h41216c.1
        have p41216_1 := h41216c.2.1
        have p41216_2 := h41216c.2.2.1
        have p41216_3 := h41216c.2.2.2
        linarith only [hlam, p41216_0]
  · rcases m.htr 3 4 5 (by decide) (by decide) with h41314 | h41314
    · linarith only [h0, h41027, h41039, h41041, h41314, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
    · rcases h1bigk with h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c | h41316c
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h0, hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h33187, hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h36828, hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h39227, hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        rcases p41316_3 (m.d 0 1) (by simp) with h41322 | h41322
        · linarith only [h41322, hlam, p41316_0]
        · rcases p41316_3 (m.d 1 2) (by simp) with h41324 | h41324
          · rcases p41316_3 (m.d 1 3) (by simp) with h41325 | h41325
            · linarith only [h41033, h41325, hlam]
            · linarith only [h33187, h41325, hlam]
          · linarith only [h41324, hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h33187, hc01, hc12, hlam, hphi, p41316_1]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h36828, hc01, hc12, hlam, hphi, p41316_1]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h39227, hc01, hc12, hlam, hphi, p41316_1]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        rcases p41316_3 (m.d 0 1) (by simp) with h41333 | h41333
        · linarith only [h41333, hlam, p41316_0]
        · rcases p41316_3 (m.d 1 2) (by simp) with h41335 | h41335
          · rcases p41316_3 (m.d 1 3) (by simp) with h41336 | h41336
            · rcases p41316_3 (m.d 1 4) (by simp) with h41337 | h41337
              · linarith only [h41036, h41337, hlam]
              · linarith only [h36828, h41337, hlam]
            · linarith only [h41336, hlam, p41316_0]
          · linarith only [h0, h41335, hlam]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h41033, hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h36828, hc01, hc13, hlam, hphi, p41316_1]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h39227, h41033, hc01, hc12, hlam, hphi, p41316_1]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        rcases p41316_3 (m.d 0 1) (by simp) with h41346 | h41346
        · linarith only [h41346, hlam, p41316_0]
        · rcases p41316_3 (m.d 1 2) (by simp) with h41348 | h41348
          · rcases p41316_3 (m.d 1 3) (by simp) with h41349 | h41349
            · rcases p41316_3 (m.d 1 4) (by simp) with h41350 | h41350
              · rcases p41316_3 (m.d 1 5) (by simp) with h41351 | h41351
                · linarith only [h41038, h41351, hlam]
                · linarith only [h39227, h41351, hlam]
              · linarith only [h41350, hlam, p41316_0]
            · linarith only [h33187, h41349, hlam]
          · linarith only [h0, h41348, hlam]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h41034, hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h41036, hlam, p41316_1]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h39227, hc01, hc14, hlam, hphi, p41316_1]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        rcases p41316_3 (m.d 0 1) (by simp) with h41361 | h41361
        · linarith only [h41361, hlam, p41316_0]
        · rcases p41316_3 (m.d 1 2) (by simp) with h41363 | h41363
          · rcases p41316_3 (m.d 1 3) (by simp) with h41364 | h41364
            · rcases p41316_3 (m.d 1 4) (by simp) with h41365 | h41365
              · rcases p41316_3 (m.d 1 5) (by simp) with h41366 | h41366
                · rcases h1emax with h41367 | h41367 | h41367 | h41367 | h41367
                  · rcases h2bigk with h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c | h41368c
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [h0, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      rcases p41368_3 (m.d 0 2) (by simp) with h41371 | h41371
                      · rcases p41368_3 (m.d 1 2) (by simp) with h41372 | h41372
                        · rcases p41368_3 (m.d 2 3) (by simp) with h41373 | h41373
                          · linarith only [h41373, hlam, p41368_0]
                          · rcases p41368_3 (m.d 2 4) (by simp) with h41375 | h41375
                            · linarith only [h41028, h41375, hlam]
                            · rcases p41368_3 (m.d 2 5) (by simp) with h41377 | h41377
                              · linarith only [h41029, h41377, hlam]
                              · rcases h4bigk with h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c | h41379c
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h36828, hlam, p41379_1]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  rcases p41379_3 (m.d 0 4) (by simp) with h41382 | h41382
                                  · rcases p41379_3 (m.d 1 4) (by simp) with h41383 | h41383
                                    · rcases p41379_3 (m.d 2 4) (by simp) with h41384 | h41384
                                      · linarith only [h41028, h41384, hlam]
                                      · rcases p41379_3 (m.d 3 4) (by simp) with h41386 | h41386
                                        · linarith only [h41030, h41386, hlam]
                                        · rcases p41379_3 (m.d 4 5) (by simp) with h41388 | h41388
                                          · linarith only [h41032, h41388, hlam]
                                          · linarith only [h41041, h41388, hlam]
                                    · linarith only [h41034, h41383, hlam]
                                  · linarith only [h41028, h41382, hlam]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  rcases p41379_3 (m.d 0 4) (by simp) with h41393 | h41393
                                  · rcases p41379_3 (m.d 1 4) (by simp) with h41394 | h41394
                                    · rcases p41379_3 (m.d 2 4) (by simp) with h41395 | h41395
                                      · linarith only [h41028, h41395, hlam]
                                      · linarith only [h41039, h41395, hlam]
                                    · linarith only [h41036, h41394, hlam]
                                  · linarith only [h41030, h41393, hlam]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  rcases p41379_3 (m.d 0 4) (by simp) with h41400 | h41400
                                  · rcases p41379_3 (m.d 1 4) (by simp) with h41401 | h41401
                                    · rcases p41379_3 (m.d 2 4) (by simp) with h41402 | h41402
                                      · linarith only [h41028, h41402, hlam]
                                      · rcases p41379_3 (m.d 3 4) (by simp) with h41404 | h41404
                                        · linarith only [h41030, h41404, hlam]
                                        · rcases p41379_3 (m.d 4 5) (by simp) with h41406 | h41406
                                          · linarith only [h41406, hlam, p41379_0]
                                          · rcases h5bigk with h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c | h41408c
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [hlam, p41408_0]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h39227, hlam, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              rcases p41408_3 (m.d 0 5) (by simp) with h41411 | h41411
                                              · rcases p41408_3 (m.d 1 5) (by simp) with h41412 | h41412
                                                · rcases p41408_3 (m.d 2 5) (by simp) with h41413 | h41413
                                                  · linarith only [h41029, h41413, hlam]
                                                  · rcases p41408_3 (m.d 3 5) (by simp) with h41415 | h41415
                                                    · linarith only [h41031, h41415, hlam]
                                                    · rcases p41408_3 (m.d 4 5) (by simp) with h41417 | h41417
                                                      · linarith only [h41032, h41417, hlam]
                                                      · linarith only [h41041, h41417, hlam]
                                                · linarith only [h41035, h41412, hlam]
                                              · linarith only [h41029, h41411, hlam]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              rcases p41408_3 (m.d 0 5) (by simp) with h41422 | h41422
                                              · rcases p41408_3 (m.d 1 5) (by simp) with h41423 | h41423
                                                · rcases p41408_3 (m.d 2 5) (by simp) with h41424 | h41424
                                                  · linarith only [h41029, h41424, hlam]
                                                  · linarith only [h41040, h41424, hlam]
                                                · linarith only [h41037, h41423, hlam]
                                              · linarith only [h41031, h41422, hlam]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h41032, h41039, h41041, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h39227, hc01, hc15, hlam, hphi, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [hlam, p41408_0]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              rcases p41408_3 (m.d 0 5) (by simp) with h41432 | h41432
                                              · linarith only [h39227, h41432, hlam]
                                              · linarith only [h41029, h41432, hlam]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              rcases p41408_3 (m.d 0 5) (by simp) with h41435 | h41435
                                              · linarith only [h39227, h41435, hlam]
                                              · linarith only [h41031, h41435, hlam]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h41033, h41036, h41038, h41039, h41041, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h41029, hlam, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h41035, hlam, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [hlam, p41408_0]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h0, h41029, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h41041, hlam, p41408_0]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h41031, hlam, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h41037, hlam, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h41040, hlam, p41408_0]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [hlam, p41408_0]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h41314, hlam, p41408_0]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h41032, hlam, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h41038, hlam, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h36828, h41033, h41036, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p41379_1, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [h36828, h41033, h41036, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p41379_1, p41408_1]
                                            · have p41408_0 := h41408c.1
                                              have p41408_1 := h41408c.2.1
                                              have p41408_2 := h41408c.2.2.1
                                              have p41408_3 := h41408c.2.2.2
                                              linarith only [hlam, p41408_0]
                                    · linarith only [h41038, h41401, hlam]
                                  · linarith only [h41400, hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h41032, h41033, h41036, h41039, h41041, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41379_1]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  rcases p41379_3 (m.d 0 4) (by simp) with h41458 | h41458
                                  · linarith only [h36828, h41458, hlam]
                                  · linarith only [h41028, h41458, hlam]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  rcases p41379_3 (m.d 0 4) (by simp) with h41461 | h41461
                                  · linarith only [h36828, h41461, hlam]
                                  · linarith only [h41030, h41461, hlam]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  rcases p41379_3 (m.d 0 4) (by simp) with h41464 | h41464
                                  · linarith only [h36828, h41464, hlam]
                                  · linarith only [h41032, h41464, hlam]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h41028, hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h41034, hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h41032, h41041, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p41379_1]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h41041, hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h41030, hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h41036, hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h41039, hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h41314, hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h41032, hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [h41038, hlam, p41379_0]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  rcases p41379_3 (m.d 0 4) (by simp) with h41479 | h41479
                                  · rcases p41379_3 (m.d 1 4) (by simp) with h41480 | h41480
                                    · rcases p41379_3 (m.d 2 4) (by simp) with h41481 | h41481
                                      · linarith only [h41481, hlam, p41379_0]
                                      · rcases p41379_3 (m.d 3 4) (by simp) with h41483 | h41483
                                        · linarith only [h41314, h41483, hlam]
                                        · rcases p41379_3 (m.d 4 5) (by simp) with h41485 | h41485
                                          · rcases h5bigk with h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c | h41486c
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [hlam, p41486_0]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h39227, hlam, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              rcases p41486_3 (m.d 0 5) (by simp) with h41489 | h41489
                                              · rcases p41486_3 (m.d 1 5) (by simp) with h41490 | h41490
                                                · rcases p41486_3 (m.d 2 5) (by simp) with h41491 | h41491
                                                  · linarith only [h41029, h41491, hlam]
                                                  · rcases p41486_3 (m.d 3 5) (by simp) with h41493 | h41493
                                                    · linarith only [h41031, h41493, hlam]
                                                    · rcases p41486_3 (m.d 4 5) (by simp) with h41495 | h41495
                                                      · linarith only [h41032, h41495, hlam]
                                                      · linarith only [h41041, h41495, hlam]
                                                · linarith only [h41035, h41490, hlam]
                                              · linarith only [h41029, h41489, hlam]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              rcases p41486_3 (m.d 0 5) (by simp) with h41500 | h41500
                                              · rcases p41486_3 (m.d 1 5) (by simp) with h41501 | h41501
                                                · rcases p41486_3 (m.d 2 5) (by simp) with h41502 | h41502
                                                  · linarith only [h41029, h41502, hlam]
                                                  · linarith only [h41040, h41502, hlam]
                                                · linarith only [h41037, h41501, hlam]
                                              · linarith only [h41031, h41500, hlam]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h39227, h41033, h41036, h41038, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p41379_1, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h39227, h41033, h41036, h41038, hc01, hc12, hlam, hphi, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [hlam, p41486_0]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              rcases p41486_3 (m.d 0 5) (by simp) with h41510 | h41510
                                              · linarith only [h39227, h41510, hlam]
                                              · linarith only [h41029, h41510, hlam]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              rcases p41486_3 (m.d 0 5) (by simp) with h41513 | h41513
                                              · linarith only [h39227, h41513, hlam]
                                              · linarith only [h41031, h41513, hlam]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h41033, h41036, h41038, h41039, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41379_1, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h41029, hlam, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h41035, hlam, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [hlam, p41486_0]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h0, h41029, h41314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h41041, hlam, p41486_0]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h41031, hlam, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h41037, hlam, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h41040, hlam, p41486_0]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [hlam, p41486_0]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h41314, hlam, p41486_0]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h41032, hlam, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h41038, hlam, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h0, h41027, h41030, h41032, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [h0, h41027, h41030, h41032, h41314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41486_1]
                                            · have p41486_0 := h41486c.1
                                              have p41486_1 := h41486c.2.1
                                              have p41486_2 := h41486c.2.2.1
                                              have p41486_3 := h41486c.2.2.2
                                              linarith only [hlam, p41486_0]
                                          · linarith only [h41485, hlam, p41379_0]
                                    · linarith only [h41034, h41480, hlam]
                                  · linarith only [h41028, h41479, hlam]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  rcases p41379_3 (m.d 0 4) (by simp) with h41535 | h41535
                                  · rcases p41379_3 (m.d 1 4) (by simp) with h41536 | h41536
                                    · rcases p41379_3 (m.d 2 4) (by simp) with h41537 | h41537
                                      · linarith only [h41041, h41537, hlam]
                                      · linarith only [h41039, h41537, hlam]
                                    · linarith only [h41036, h41536, hlam]
                                  · linarith only [h41030, h41535, hlam]
                                · have p41379_0 := h41379c.1
                                  have p41379_1 := h41379c.2.1
                                  have p41379_2 := h41379c.2.2.1
                                  have p41379_3 := h41379c.2.2.2
                                  linarith only [hlam, p41379_0]
                        · linarith only [h41033, h41372, hlam]
                      · linarith only [h41371, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      rcases p41368_3 (m.d 0 2) (by simp) with h41545 | h41545
                      · rcases p41368_3 (m.d 1 2) (by simp) with h41546 | h41546
                        · rcases p41368_3 (m.d 2 3) (by simp) with h41547 | h41547
                          · linarith only [h41027, h41547, hlam]
                          · linarith only [h41039, h41547, hlam]
                        · linarith only [h41034, h41546, hlam]
                      · linarith only [h41545, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      rcases p41368_3 (m.d 0 2) (by simp) with h41552 | h41552
                      · rcases p41368_3 (m.d 1 2) (by simp) with h41553 | h41553
                        · rcases p41368_3 (m.d 2 3) (by simp) with h41554 | h41554
                          · linarith only [h41027, h41554, hlam]
                          · linarith only [h41040, h41554, hlam]
                        · linarith only [h41035, h41553, hlam]
                      · linarith only [h41552, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [h41027, h41039, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41368_1]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      rcases p41368_3 (m.d 0 2) (by simp) with h41561 | h41561
                      · linarith only [h0, h41561, hlam]
                      · linarith only [h41027, h41561, hlam]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      rcases p41368_3 (m.d 0 2) (by simp) with h41564 | h41564
                      · linarith only [h0, h41564, hlam]
                      · linarith only [h41028, h41564, hlam]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      rcases p41368_3 (m.d 0 2) (by simp) with h41567 | h41567
                      · linarith only [h0, h41567, hlam]
                      · linarith only [h41029, h41567, hlam]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [h41027, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [h41033, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      rcases p41368_3 (m.d 0 2) (by simp) with h41573 | h41573
                      · rcases p41368_3 (m.d 1 2) (by simp) with h41574 | h41574
                        · rcases p41368_3 (m.d 2 3) (by simp) with h41575 | h41575
                          · rcases p41368_3 (m.d 2 4) (by simp) with h41576 | h41576
                            · linarith only [h41039, h41576, hlam]
                            · rcases p41368_3 (m.d 2 5) (by simp) with h41578 | h41578
                              · linarith only [h41040, h41578, hlam]
                              · linarith only [h41041, h41578, hlam]
                          · linarith only [h41039, h41575, hlam]
                        · linarith only [h41034, h41574, hlam]
                      · linarith only [h41028, h41573, hlam]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      rcases p41368_3 (m.d 0 2) (by simp) with h41584 | h41584
                      · rcases p41368_3 (m.d 1 2) (by simp) with h41585 | h41585
                        · rcases p41368_3 (m.d 2 3) (by simp) with h41586 | h41586
                          · rcases p41368_3 (m.d 2 4) (by simp) with h41587 | h41587
                            · linarith only [h41039, h41587, hlam]
                            · rcases p41368_3 (m.d 2 5) (by simp) with h41589 | h41589
                              · linarith only [h41040, h41589, hlam]
                              · rcases h4bigk with h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c | h41591c
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h36828, hlam, p41591_1]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  rcases p41591_3 (m.d 0 4) (by simp) with h41594 | h41594
                                  · rcases p41591_3 (m.d 1 4) (by simp) with h41595 | h41595
                                    · rcases p41591_3 (m.d 2 4) (by simp) with h41596 | h41596
                                      · linarith only [h41028, h41596, hlam]
                                      · rcases p41591_3 (m.d 3 4) (by simp) with h41598 | h41598
                                        · linarith only [h41030, h41598, hlam]
                                        · rcases p41591_3 (m.d 4 5) (by simp) with h41600 | h41600
                                          · linarith only [h41032, h41600, hlam]
                                          · linarith only [h41041, h41600, hlam]
                                    · linarith only [h41034, h41595, hlam]
                                  · linarith only [h41028, h41594, hlam]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  rcases p41591_3 (m.d 0 4) (by simp) with h41605 | h41605
                                  · rcases p41591_3 (m.d 1 4) (by simp) with h41606 | h41606
                                    · rcases p41591_3 (m.d 2 4) (by simp) with h41607 | h41607
                                      · linarith only [h41028, h41607, hlam]
                                      · linarith only [h41039, h41607, hlam]
                                    · linarith only [h41036, h41606, hlam]
                                  · linarith only [h41030, h41605, hlam]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  rcases p41591_3 (m.d 0 4) (by simp) with h41612 | h41612
                                  · rcases p41591_3 (m.d 1 4) (by simp) with h41613 | h41613
                                    · rcases p41591_3 (m.d 2 4) (by simp) with h41614 | h41614
                                      · linarith only [h41028, h41614, hlam]
                                      · rcases p41591_3 (m.d 3 4) (by simp) with h41616 | h41616
                                        · linarith only [h41030, h41616, hlam]
                                        · rcases p41591_3 (m.d 4 5) (by simp) with h41618 | h41618
                                          · linarith only [h41618, hlam, p41591_0]
                                          · rcases h5bigk with h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c | h41620c
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [hlam, p41620_0]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h39227, hlam, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              rcases p41620_3 (m.d 0 5) (by simp) with h41623 | h41623
                                              · rcases p41620_3 (m.d 1 5) (by simp) with h41624 | h41624
                                                · rcases p41620_3 (m.d 2 5) (by simp) with h41625 | h41625
                                                  · linarith only [h41029, h41625, hlam]
                                                  · rcases p41620_3 (m.d 3 5) (by simp) with h41627 | h41627
                                                    · linarith only [h41031, h41627, hlam]
                                                    · rcases p41620_3 (m.d 4 5) (by simp) with h41629 | h41629
                                                      · linarith only [h41032, h41629, hlam]
                                                      · linarith only [h41041, h41629, hlam]
                                                · linarith only [h41035, h41624, hlam]
                                              · linarith only [h41029, h41623, hlam]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              rcases p41620_3 (m.d 0 5) (by simp) with h41634 | h41634
                                              · rcases p41620_3 (m.d 1 5) (by simp) with h41635 | h41635
                                                · rcases p41620_3 (m.d 2 5) (by simp) with h41636 | h41636
                                                  · linarith only [h41029, h41636, hlam]
                                                  · linarith only [h41040, h41636, hlam]
                                                · linarith only [h41037, h41635, hlam]
                                              · linarith only [h41031, h41634, hlam]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41027, h41030, h41032, h41039, h41041, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h39227, h41033, h41036, h41038, hc01, hc12, hlam, hphi, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [hlam, p41620_0]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              rcases p41620_3 (m.d 0 5) (by simp) with h41644 | h41644
                                              · linarith only [h39227, h41644, hlam]
                                              · linarith only [h41029, h41644, hlam]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              rcases p41620_3 (m.d 0 5) (by simp) with h41647 | h41647
                                              · linarith only [h39227, h41647, hlam]
                                              · linarith only [h41031, h41647, hlam]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41033, h41036, h41038, h41039, h41041, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41029, hlam, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41035, hlam, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [hlam, p41620_0]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41314, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p41368_1, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41041, hlam, p41620_0]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41031, hlam, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41037, hlam, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41040, hlam, p41620_0]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [hlam, p41620_0]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41314, hlam, p41620_0]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41032, hlam, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h41038, hlam, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h0, h41027, h41030, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p41591_1, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [h0, h41027, h41030, h41314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41591_1, p41620_1]
                                            · have p41620_0 := h41620c.1
                                              have p41620_1 := h41620c.2.1
                                              have p41620_2 := h41620c.2.2.1
                                              have p41620_3 := h41620c.2.2.2
                                              linarith only [hlam, p41620_0]
                                    · linarith only [h41038, h41613, hlam]
                                  · linarith only [h41612, hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h41032, h41033, h41036, h41039, h41041, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41591_1]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  rcases p41591_3 (m.d 0 4) (by simp) with h41670 | h41670
                                  · linarith only [h36828, h41670, hlam]
                                  · linarith only [h41028, h41670, hlam]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  rcases p41591_3 (m.d 0 4) (by simp) with h41673 | h41673
                                  · linarith only [h36828, h41673, hlam]
                                  · linarith only [h41030, h41673, hlam]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  rcases p41591_3 (m.d 0 4) (by simp) with h41676 | h41676
                                  · linarith only [h36828, h41676, hlam]
                                  · linarith only [h41032, h41676, hlam]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h41028, hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h41034, hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h41032, h41041, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p41591_1]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h41041, hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h41030, hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h41036, hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h41039, hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h41314, hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h41032, hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [h41038, hlam, p41591_0]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  rcases p41591_3 (m.d 0 4) (by simp) with h41691 | h41691
                                  · rcases p41591_3 (m.d 1 4) (by simp) with h41692 | h41692
                                    · rcases p41591_3 (m.d 2 4) (by simp) with h41693 | h41693
                                      · linarith only [h41693, hlam, p41591_0]
                                      · rcases p41591_3 (m.d 3 4) (by simp) with h41695 | h41695
                                        · linarith only [h41314, h41695, hlam]
                                        · rcases p41591_3 (m.d 4 5) (by simp) with h41697 | h41697
                                          · rcases h5bigk with h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c | h41698c
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [hlam, p41698_0]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h39227, hlam, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              rcases p41698_3 (m.d 0 5) (by simp) with h41701 | h41701
                                              · rcases p41698_3 (m.d 1 5) (by simp) with h41702 | h41702
                                                · rcases p41698_3 (m.d 2 5) (by simp) with h41703 | h41703
                                                  · linarith only [h41029, h41703, hlam]
                                                  · rcases p41698_3 (m.d 3 5) (by simp) with h41705 | h41705
                                                    · linarith only [h41031, h41705, hlam]
                                                    · rcases p41698_3 (m.d 4 5) (by simp) with h41707 | h41707
                                                      · linarith only [h41032, h41707, hlam]
                                                      · linarith only [h41041, h41707, hlam]
                                                · linarith only [h41035, h41702, hlam]
                                              · linarith only [h41029, h41701, hlam]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              rcases p41698_3 (m.d 0 5) (by simp) with h41712 | h41712
                                              · rcases p41698_3 (m.d 1 5) (by simp) with h41713 | h41713
                                                · rcases p41698_3 (m.d 2 5) (by simp) with h41714 | h41714
                                                  · linarith only [h41029, h41714, hlam]
                                                  · linarith only [h41040, h41714, hlam]
                                                · linarith only [h41037, h41713, hlam]
                                              · linarith only [h41031, h41712, hlam]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h39227, h41033, h41036, h41038, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p41591_1, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h39227, h41033, h41036, h41038, hc01, hc12, hlam, hphi, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [hlam, p41698_0]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              rcases p41698_3 (m.d 0 5) (by simp) with h41722 | h41722
                                              · linarith only [h39227, h41722, hlam]
                                              · linarith only [h41029, h41722, hlam]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              rcases p41698_3 (m.d 0 5) (by simp) with h41725 | h41725
                                              · linarith only [h39227, h41725, hlam]
                                              · linarith only [h41031, h41725, hlam]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h41033, h41036, h41038, h41039, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41591_1, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h41029, hlam, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h41035, hlam, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [hlam, p41698_0]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h0, h41029, h41314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h41041, hlam, p41698_0]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h41031, hlam, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h41037, hlam, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h41040, hlam, p41698_0]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [hlam, p41698_0]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h41314, hlam, p41698_0]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h41032, hlam, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h41038, hlam, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h0, h41027, h41030, h41032, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [h0, h41027, h41030, h41032, h41314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41698_1]
                                            · have p41698_0 := h41698c.1
                                              have p41698_1 := h41698c.2.1
                                              have p41698_2 := h41698c.2.2.1
                                              have p41698_3 := h41698c.2.2.2
                                              linarith only [hlam, p41698_0]
                                          · linarith only [h41697, hlam, p41591_0]
                                    · linarith only [h41034, h41692, hlam]
                                  · linarith only [h41028, h41691, hlam]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  rcases p41591_3 (m.d 0 4) (by simp) with h41747 | h41747
                                  · rcases p41591_3 (m.d 1 4) (by simp) with h41748 | h41748
                                    · rcases p41591_3 (m.d 2 4) (by simp) with h41749 | h41749
                                      · linarith only [h41041, h41749, hlam]
                                      · linarith only [h41039, h41749, hlam]
                                    · linarith only [h41036, h41748, hlam]
                                  · linarith only [h41030, h41747, hlam]
                                · have p41591_0 := h41591c.1
                                  have p41591_1 := h41591c.2.1
                                  have p41591_2 := h41591c.2.2.1
                                  have p41591_3 := h41591c.2.2.2
                                  linarith only [hlam, p41591_0]
                          · linarith only [h41040, h41586, hlam]
                        · linarith only [h41035, h41585, hlam]
                      · linarith only [h41029, h41584, hlam]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [h41028, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [h41034, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [h41039, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [h41041, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [h41029, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [h41035, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [h41040, hlam, p41368_0]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      rcases p41368_3 (m.d 0 2) (by simp) with h41766 | h41766
                      · rcases p41368_3 (m.d 1 2) (by simp) with h41767 | h41767
                        · rcases p41368_3 (m.d 2 3) (by simp) with h41768 | h41768
                          · rcases p41368_3 (m.d 2 4) (by simp) with h41769 | h41769
                            · linarith only [h41041, h41769, hlam]
                            · rcases p41368_3 (m.d 2 5) (by simp) with h41771 | h41771
                              · rcases h4bigk with h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c | h41772c
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h36828, hlam, p41772_1]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41032, h41041, hlam, p41368_1, p41772_2]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41032, h41039, h41041, hlam, p41368_1, p41772_2]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h36828, h41033, h41036, h41041, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p41368_1, p41772_1]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41032, h41033, h41036, h41039, h41041, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41368_1, p41772_1]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h36828, h41032, h41041, hlam, p41368_1, p41772_2]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h36828, h41032, h41039, h41041, hlam, p41368_1, p41772_2]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41039, h41041, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41368_1, p41772_1]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41028, hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41034, hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41032, h41041, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p41368_1, p41772_1]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41041, hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41030, hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41036, hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41039, hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41314, hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41032, hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [h41038, hlam, p41772_0]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  rcases p41772_3 (m.d 0 4) (by simp) with h41795 | h41795
                                  · rcases p41772_3 (m.d 1 4) (by simp) with h41796 | h41796
                                    · rcases p41772_3 (m.d 2 4) (by simp) with h41797 | h41797
                                      · linarith only [h41797, hlam, p41772_0]
                                      · rcases p41772_3 (m.d 3 4) (by simp) with h41799 | h41799
                                        · linarith only [h41314, h41799, hlam]
                                        · rcases p41772_3 (m.d 4 5) (by simp) with h41801 | h41801
                                          · rcases h5bigk with h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c | h41802c
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [hlam, p41802_0]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h39227, hlam, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p41368_1, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              rcases p41802_3 (m.d 0 5) (by simp) with h41806 | h41806
                                              · rcases p41802_3 (m.d 1 5) (by simp) with h41807 | h41807
                                                · rcases p41802_3 (m.d 2 5) (by simp) with h41808 | h41808
                                                  · linarith only [h41029, h41808, hlam]
                                                  · linarith only [h41040, h41808, hlam]
                                                · linarith only [h41037, h41807, hlam]
                                              · linarith only [h41031, h41806, hlam]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h39227, h41033, h41036, h41038, h41039, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41772_1, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h39227, h41033, h41036, h41038, hc01, hc12, hlam, hphi, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [hlam, p41802_0]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41033, h41036, h41038, h41039, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41368_1, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              rcases p41802_3 (m.d 0 5) (by simp) with h41817 | h41817
                                              · linarith only [h39227, h41817, hlam]
                                              · linarith only [h41031, h41817, hlam]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41033, h41036, h41038, h41039, h41041, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41368_1, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41029, hlam, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41035, hlam, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [hlam, p41802_0]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41041, h41314, hc34, hc45, hlam, hphi, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41041, hlam, p41802_0]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41031, hlam, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41037, hlam, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41040, hlam, p41802_0]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [hlam, p41802_0]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41314, hlam, p41802_0]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41032, hlam, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h41038, hlam, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h0, h41027, h41030, h41032, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [h0, h41027, h41030, h41032, h41314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p41802_1]
                                            · have p41802_0 := h41802c.1
                                              have p41802_1 := h41802c.2.1
                                              have p41802_2 := h41802c.2.2.1
                                              have p41802_3 := h41802c.2.2.2
                                              linarith only [hlam, p41802_0]
                                          · linarith only [h41801, hlam, p41772_0]
                                    · linarith only [h41034, h41796, hlam]
                                  · linarith only [h41028, h41795, hlam]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  rcases p41772_3 (m.d 0 4) (by simp) with h41839 | h41839
                                  · rcases p41772_3 (m.d 1 4) (by simp) with h41840 | h41840
                                    · rcases p41772_3 (m.d 2 4) (by simp) with h41841 | h41841
                                      · linarith only [h41041, h41841, hlam]
                                      · linarith only [h41039, h41841, hlam]
                                    · linarith only [h41036, h41840, hlam]
                                  · linarith only [h41030, h41839, hlam]
                                · have p41772_0 := h41772c.1
                                  have p41772_1 := h41772c.2.1
                                  have p41772_2 := h41772c.2.2.1
                                  have p41772_3 := h41772c.2.2.2
                                  linarith only [hlam, p41772_0]
                              · linarith only [h41041, h41771, hlam]
                          · linarith only [h41039, h41768, hlam]
                        · linarith only [h41034, h41767, hlam]
                      · linarith only [h41028, h41766, hlam]
                    · have p41368_0 := h41368c.1
                      have p41368_1 := h41368c.2.1
                      have p41368_2 := h41368c.2.2.1
                      have p41368_3 := h41368c.2.2.2
                      linarith only [hlam, p41368_0]
                  · linarith only [h0, h41367, hc01, hlam]
                  · linarith only [h41036, h41038, h41367, hc01, hlam, p41316_1]
                  · linarith only [h41038, h41367, hc01, hlam, p41316_1]
                  · linarith only [h41367, hc01, hlam, p41316_1]
                · linarith only [h41366, hlam, p41316_0]
              · linarith only [h36828, h41365, hlam]
            · linarith only [h33187, h41364, hlam]
          · linarith only [h0, h41363, hlam]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h41035, hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h41037, hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [h41038, hlam, p41316_0]
      · have p41316_0 := h41316c.1
        have p41316_1 := h41316c.2.1
        have p41316_2 := h41316c.2.2.1
        have p41316_3 := h41316c.2.2.2
        linarith only [hlam, p41316_0]

end R2N4
