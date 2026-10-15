import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1337 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1673 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1959 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1960 | h1960
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1961 | h1961
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1962 | h1962
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1963 | h1963
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1964 | h1964
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1965 | h1965
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1966 | h1966
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1967 | h1967
                · rcases h0bigk with h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [hlam, p1968_0]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h0, hlam, p1968_1]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1337, hlam, p1968_0]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1673, hlam, p1968_1]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1673, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1968_1]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1968_1]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [hlam, p1968_0]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h0, h1960, h1967, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1968_1, u3ehi3]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h0, h1673, h1959, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1968_1]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h0, h1964, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1968_1, u3ehi4]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1959, h1964, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1968_1, u3ehi4]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1960, hlam, p1968_1]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [hlam, p1968_0]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h0, h1673, h1959, h1960, h1964, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1968_1, u3ehi4]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h0, h1960, h1964, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1968_1, u3ehi4]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1959, h1964, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1968_1, u3ehi4]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1961, hlam, p1968_0]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1963, hlam, p1968_0]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [hlam, p1968_0]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h0, h1960, h1963, h1964, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1968_1, u3ehi4]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1959, hlam, p1968_0]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1962, hlam, p1968_1]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1964, hlam, p1968_0]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [h1965, hlam, p1968_1]
                  · have p1968_0 := h1968c.1
                    have p1968_1 := h1968c.2.1
                    have p1968_2 := h1968c.2.2.1
                    have p1968_3 := h1968c.2.2.2
                    linarith only [hlam, p1968_0]
                · rcases h0bigk with h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [hlam, p1994_0]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h0, hlam, p1994_1]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1337, hlam, p1994_0]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1673, hlam, p1994_1]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1964, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1994_1, u3ehi4]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1994_1]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [hlam, p1994_0]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1994_1, u3ehi0]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h0, h1673, h1959, h1964, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1994_1, u3ehi4]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h0, h1964, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1994_1, u3ehi4]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1959, h1964, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1994_1, u3ehi4]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1960, hlam, p1994_1]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [hlam, p1994_0]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h0, h1673, h1959, h1960, h1964, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1994_1, u3ehi4]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h0, h1960, h1964, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1994_1, u3ehi4]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1959, h1964, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1994_1, u3ehi4]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1961, hlam, p1994_0]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1963, hlam, p1994_0]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [hlam, p1994_0]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h0, h1960, h1963, h1964, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1994_1, u3ehi4]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1959, hlam, p1994_0]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1962, hlam, p1994_1]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1964, hlam, p1994_0]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [h1965, hlam, p1994_1]
                  · have p1994_0 := h1994c.1
                    have p1994_1 := h1994c.2.1
                    have p1994_2 := h1994c.2.2.1
                    have p1994_3 := h1994c.2.2.2
                    linarith only [hlam, p1994_0]
              · linarith only [h0, h1961, h1966, hlam]
            · linarith only [h1673, h1959, h1965, hlam]
          · linarith only [h1963, h1964, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2023 | h2023
          · linarith only [h1963, h2023, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1337, h1959, h2023, hlam]
      · linarith only [h0, h1959, h1962, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2027 | h2027
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2028 | h2028
        · linarith only [h1960, h1961, h2028, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2030 | h2030
          · linarith only [h2028, h2030, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1337, h1959, h2030, hlam]
      · linarith only [h0, h1959, h2027, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2034 | h2034
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2035 | h2035
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2036 | h2036
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2037 | h2037
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2038 | h2038
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2039 | h2039
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2040 | h2040
                · rcases h0bigk with h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [hlam, p2041_0]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h0, hlam, p2041_1]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1337, hlam, p2041_0]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1673, hlam, p2041_1]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1673, h2039, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2041_1]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1960, hc01, hc23, hlam, hphi, ht12, p2041_1]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [hlam, p2041_0]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1960, hlam, p2041_0]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1673, h1959, h1960, h2037, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2041_1, u3ehi4]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1960, h2037, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2041_1, u3ehi4]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1959, h2037, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p2041_1, u3ehi4]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1960, hc02, hc23, hlam, hphi, p2041_1]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [hlam, p2041_0]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1673, h1959, h1960, h2037, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2041_1, u3ehi4]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1960, h2037, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2041_1, u3ehi4]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1959, h2034, h2037, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p2041_1, u3ehi4]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h2034, hlam, p2041_0]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h2036, hlam, p2041_0]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [hlam, p2041_0]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1960, h2034, h2037, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2041_1, u3ehi4]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h1959, hlam, p2041_0]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h2035, hlam, p2041_1]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h2037, hlam, p2041_0]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [h2038, hlam, p2041_1]
                  · have p2041_0 := h2041c.1
                    have p2041_1 := h2041c.2.1
                    have p2041_2 := h2041c.2.2.1
                    have p2041_3 := h2041c.2.2.2
                    linarith only [hlam, p2041_0]
                · linarith only [h0, h1959, h1960, h2037, h2040, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1960, h2034, h2039, hc12, hc23, hlam, hphi]
            · linarith only [h1673, h1959, h2038, hlam]
          · linarith only [h2036, h2037, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1960, h2034, h2036, hlam]
      · linarith only [h0, h1959, h2035, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2073 | h2073
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2074 | h2074
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2075 | h2075
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2076 | h2076
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2077 | h2077
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2078 | h2078
                · rcases h0bigk with h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [hlam, p2079_0]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h0, hlam, p2079_1]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h1337, hlam, p2079_0]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h1673, hlam, p2079_1]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h0, h2034, h2077, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2079_1]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h2034, h2077, hc01, hc12, hlam, hphi, p2079_1]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [hlam, p2079_0]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h1960, hlam, p2079_0]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h2034, hlam, p2079_1]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h1959, h2034, h2077, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p2079_1]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h1959, hc03, hc15, hlam, hphi, ht0b, ht5b, p2079_1]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h1960, hc02, hc23, hlam, hphi, p2079_1]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [hlam, p2079_0]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h0, h1959, h1960, h2034, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2079_1]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h1960, h2075, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2079_1, u3ehi4]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h1959, h2075, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2079_1, u3ehi4]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h0, h1959, h2034, h2075, h2077, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2079_1, u3ehi4]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h2074, hlam, p2079_0]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [hlam, p2079_0]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h2034, h2075, h2077, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2079_1, u3ehi4]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h1959, hlam, p2079_0]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h2073, hlam, p2079_1]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h2075, hlam, p2079_0]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [h2076, hlam, p2079_1]
                  · have p2079_0 := h2079c.1
                    have p2079_1 := h2079c.2.1
                    have p2079_2 := h2079c.2.2.1
                    have p2079_3 := h2079c.2.2.2
                    linarith only [hlam, p2079_0]
                · linarith only [h0, h1959, h1960, h2075, h2078, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2106 | h2106
                · rcases h0bigk with h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [hlam, p2107_0]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h0, hlam, p2107_1]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h1337, hlam, p2107_0]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h1673, hlam, p2107_1]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h2075, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p2107_1, u3ehi4]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2107_1]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [hlam, p2107_0]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h1960, hlam, p2107_0]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h2034, hlam, p2107_1]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h2075, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p2107_1, u3ehi4]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h1337, h1959, h2075, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2107_1, u3ehi4]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h1960, hc02, hc23, hlam, hphi, p2107_1]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [hlam, p2107_0]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h1960, h2076, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2107_1]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h1960, h2075, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2107_1, u3ehi4]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h1959, h2075, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2107_1, u3ehi4]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h0, h1959, h2034, h2075, h2106, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2107_1, u3ehi4]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h2074, hlam, p2107_0]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [hlam, p2107_0]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h2034, h2075, h2106, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2107_1, u3ehi4]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h1959, hlam, p2107_0]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h2073, hlam, p2107_1]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h2075, hlam, p2107_0]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [h2076, hlam, p2107_1]
                  · have p2107_0 := h2107c.1
                    have p2107_1 := h2107c.2.1
                    have p2107_2 := h2107c.2.2.1
                    have p2107_3 := h2107c.2.2.2
                    linarith only [hlam, p2107_0]
                · linarith only [h0, h1959, h1960, h2075, h2106, hc34, hlam, hphi, u3ehi4]
            · linarith only [h1673, h1959, h2076, hlam]
          · linarith only [h2074, h2075, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2136 | h2136
          · linarith only [h2074, h2136, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1337, h1959, h2136, hlam]
      · linarith only [h0, h1959, h2073, hlam]

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1337 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1673 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1959 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2140 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2141 | h2141
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2142 | h2142
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2143 | h2143
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2144 | h2144
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2145 | h2145
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2146 | h2146
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2147 | h2147
              · rcases h0bigk with h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [hlam, p2148_0]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h0, hlam, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h1337, hlam, p2148_0]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h1673, hlam, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h1959, hlam, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [hlam, p2148_0]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h0, h2140, h2147, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2148_1, u3ehi3]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h0, h2145, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h0, h1959, hc01, hc12, hlam, hphi, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h2140, hlam, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [hlam, p2148_0]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h0, h2140, h2145, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h0, h1959, h2140, hc01, hc12, hlam, hphi, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h1673, hc01, hc14, hlam, hphi, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h2141, hlam, p2148_0]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h2143, hlam, p2148_0]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [hlam, p2148_0]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h0, h2140, h2143, h2144, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2148_1, u3ehi4]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h2142, hlam, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h2144, hlam, p2148_0]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [h2145, hlam, p2148_1]
                · have p2148_0 := h2148c.1
                  have p2148_1 := h2148c.2.1
                  have p2148_2 := h2148c.2.2.1
                  have p2148_3 := h2148c.2.2.2
                  linarith only [hlam, p2148_0]
              · rcases h0bigk with h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c | h2174c
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [hlam, p2174_0]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h0, hlam, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h1337, hlam, p2174_0]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h1673, hlam, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h1959, hlam, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [hlam, p2174_0]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2174_1, u3ehi0]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h0, h1673, hc01, hc12, hlam, hphi, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h0, h1959, hc01, hc12, hlam, hphi, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h2140, hlam, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [hlam, p2174_0]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h0, h1959, h2140, h2145, hc01, hc12, hlam, hphi, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h0, h1959, h2140, hc01, hc12, hlam, hphi, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h1673, h2146, hc01, hc12, hlam, hphi, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h2141, hlam, p2174_0]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h2143, hlam, p2174_0]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [hlam, p2174_0]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h0, h2140, h2143, h2144, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2174_1, u3ehi4]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h2142, hlam, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h2144, hlam, p2174_0]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [h2145, hlam, p2174_1]
                · have p2174_0 := h2174c.1
                  have p2174_1 := h2174c.2.1
                  have p2174_2 := h2174c.2.2.1
                  have p2174_3 := h2174c.2.2.2
                  linarith only [hlam, p2174_0]
            · linarith only [h0, h2141, h2146, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2201 | h2201
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2202 | h2202
              · rcases h0bigk with h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [hlam, p2203_0]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h0, hlam, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h1337, hlam, p2203_0]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h1673, hlam, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h1959, hlam, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [hlam, p2203_0]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2203_1, u3ehi0]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h0, h1673, hc01, hc12, hlam, hphi, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h0, h1959, hc01, hc12, hlam, hphi, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h2140, hlam, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [hlam, p2203_0]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h0, h1673, h2140, hc01, hc12, hlam, hphi, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h0, h1959, h2140, hc01, hc12, hlam, hphi, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h1673, hc01, hc14, hlam, hphi, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h2141, hlam, p2203_0]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h2143, hlam, p2203_0]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [hlam, p2203_0]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h2145, hlam, p2203_0]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h2142, hlam, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h2144, hlam, p2203_0]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [h2145, hc04, hc45, hlam, hphi, p2203_1]
                · have p2203_0 := h2203c.1
                  have p2203_1 := h2203c.2.1
                  have p2203_2 := h2203c.2.2.1
                  have p2203_3 := h2203c.2.2.2
                  linarith only [hlam, p2203_0]
              · linarith only [h2143, h2145, h2202, hc45, hlam, hphi, ht34, u3ehi2]
            · linarith only [h0, h2141, h2201, hlam]
        · linarith only [h2143, h2144, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2232 | h2232
        · linarith only [h2143, h2232, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2234 | h2234
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2235 | h2235
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2236 | h2236
              · linarith only [h2140, h2143, h2236, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases h0bigk with h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [hlam, p2238_0]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h0, hlam, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h1337, hlam, p2238_0]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h1673, hlam, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h1959, hlam, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [hlam, p2238_0]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h0, h2140, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2238_1, u3ehi2]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h0, h2234, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h0, h1959, hc01, hc12, hlam, hphi, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h2140, hlam, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [hlam, p2238_0]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h2143, hlam, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h2232, hlam, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h1673, h2235, hc01, hc12, hlam, hphi, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h2141, hlam, p2238_0]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h2143, hc34, hlam, hphi, p2238_1, u3ehi0]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [hlam, p2238_0]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h2140, h2143, h2232, hc34, hlam, hphi, p2238_1, u3ehi2]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h2142, hlam, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h2140, h2232, hc35, hlam, hphi, p2238_1, u3ehi2]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [h2234, hlam, p2238_1]
                · have p2238_0 := h2238c.1
                  have p2238_1 := h2238c.2.1
                  have p2238_2 := h2238c.2.2.1
                  have p2238_3 := h2238c.2.2.2
                  linarith only [hlam, p2238_0]
            · linarith only [h0, h2141, h2235, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2265 | h2265
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2266 | h2266
              · linarith only [h2140, h2143, h2266, hlam]
              · rcases h0bigk with h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [hlam, p2268_0]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h0, hlam, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h1337, hlam, p2268_0]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h1673, hlam, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h1959, hlam, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [hlam, p2268_0]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2268_1, u3ehi0]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h0, h1673, hc01, hc12, hlam, hphi, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h0, h1959, hc01, hc12, hlam, hphi, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h2140, hlam, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [hlam, p2268_0]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h2143, hlam, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h2232, hlam, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h1673, hc01, hc14, hlam, hphi, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h2141, hlam, p2268_0]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h2143, hc34, hlam, hphi, p2268_1, u3ehi0]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [hlam, p2268_0]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h2234, hlam, p2268_0]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h2142, hlam, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h2140, h2232, hc35, hlam, hphi, p2268_1, u3ehi2]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [h2234, hc04, hc45, hlam, hphi, p2268_1]
                · have p2268_0 := h2268c.1
                  have p2268_1 := h2268c.2.1
                  have p2268_2 := h2268c.2.2.1
                  have p2268_3 := h2268c.2.2.2
                  linarith only [hlam, p2268_0]
            · linarith only [h0, h2141, h2265, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2295 | h2295
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2296 | h2296
        · linarith only [h2140, h2142, h2296, hlam]
        · linarith only [h2295, h2296, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2299 | h2299
        · linarith only [h2295, h2299, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2301 | h2301
          · linarith only [h2141, h2142, h2301, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2303 | h2303
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2304 | h2304
              · linarith only [h2140, h2142, h2304, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases h0bigk with h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [hlam, p2306_0]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h0, hlam, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h1337, hlam, p2306_0]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h1673, hlam, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h1959, hlam, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2142, hc01, hc25, hlam, hphi, ht12, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [hlam, p2306_0]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2142, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2306_1, u3ehi0]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2142, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2142, hlam, p2306_0]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2295, hc01, hc34, hlam, hphi, ht12, ht23, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2140, hlam, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [hlam, p2306_0]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2295, hlam, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2299, hlam, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h1673, h2303, hc01, hc12, hlam, hphi, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2141, hlam, p2306_0]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2141, h2142, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2306_1, u3ehi0]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [hlam, p2306_0]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2301, hlam, p2306_0]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2142, hc02, hc25, hlam, hphi, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2140, h2299, hc35, hlam, hphi, p2306_1, u3ehi2]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [h2301, hc04, hc45, hlam, hphi, p2306_1]
                · have p2306_0 := h2306c.1
                  have p2306_1 := h2306c.2.1
                  have p2306_2 := h2306c.2.2.1
                  have p2306_3 := h2306c.2.2.2
                  linarith only [hlam, p2306_0]
            · linarith only [h0, h2141, h2303, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2333 | h2333
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2334 | h2334
      · linarith only [h2140, h2141, h2334, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2336 | h2336
        · linarith only [h2334, h2336, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2338 | h2338
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2339 | h2339
            · linarith only [h2140, h2141, h2339, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2341 | h2341
              · linarith only [h2140, h2334, h2341, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h0, h2140, h2339, h2341, hc34, hlam, hphi, u3ehi2]
          · linarith only [h2140, h2141, h2338, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2345 | h2345
      · linarith only [h2140, h2141, h2345, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2347 | h2347
        · linarith only [h2345, h2347, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2349 | h2349
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2350 | h2350
            · linarith only [h2140, h2141, h2350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2352 | h2352
              · linarith only [h0, h2140, h2345, h2350, h2352, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h0, h2140, h2350, h2352, hc34, hlam, hphi, u3ehi2]
          · linarith only [h2140, h2141, h2349, hc45, hlam, hphi, ht34, u3ehi2]

end R2N4
