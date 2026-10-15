import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h958 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h959 | h959
  · rcases m.htr 0 3 5 (by decide) (by decide) with h960 | h960
    · rcases m.htr 0 4 5 (by decide) (by decide) with h961 | h961
      · rcases m.htr 1 2 3 (by decide) (by decide) with h962 | h962
        · linarith only [h3, h962, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h964 | h964
          · rcases m.htr 1 3 4 (by decide) (by decide) with h965 | h965
            · rcases m.htr 1 3 5 (by decide) (by decide) with h966 | h966
              · rcases m.htr 1 4 5 (by decide) (by decide) with h967 | h967
                · rcases m.htr 2 3 5 (by decide) (by decide) with h968 | h968
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h969 | h969
                    · rcases h0emin with h970 | h970 | h970 | h970 | h970
                      · rcases h5bigk with h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [hlam, p971_0]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h3, h958, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p971_1, u2elo2]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h3, h958, h968, h969, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p971_1, u2elo2]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h3, h958, h969, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p971_1, u2elo2]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p971_1, u2elo2]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h2, hlam, p971_0]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [hlam, p971_0]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h2, h968, h969, hc01, hc45, hlam, hphi, ht0b, ht5b, p971_1]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h2, h3, h958, h969, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p971_1, u2elo2]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h2, h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p971_1, u2elo2]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h958, hlam, p971_1]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h964, hlam, p971_1]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [hlam, p971_0]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h969, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p971_1, u2elo4]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h0, h3, h964, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p971_1, u2elo2]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h960, hlam, p971_0]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h966, hlam, p971_0]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h968, hlam, p971_0]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [hlam, p971_0]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h960, hc03, hc45, hlam, hphi, ht0b, ht5b, p971_1]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h961, hlam, p971_0]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h967, hlam, p971_0]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h965, h969, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p971_1]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [h969, hlam, p971_0]
                        · have p971_0 := h971c.1
                          have p971_1 := h971c.2.1
                          have p971_2 := h971c.2.2.1
                          have p971_3 := h971c.2.2.2
                          linarith only [hlam, p971_0]
                      · linarith only [h3, h970, hlam, ht01, ht12, u2elo2]
                      · linarith only [h3, h970, hlam, ht01, ht12, u2elo2]
                      · linarith only [h3, h959, h970, hlam, ht01, ht12, u2elo2]
                      · linarith only [h3, h958, h970, hlam, ht01, ht12, u2elo2]
                    · rcases h0emin with h1001 | h1001 | h1001 | h1001 | h1001
                      · rcases h5bigk with h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c | h1002c
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [hlam, p1002_0]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h3, h958, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1002_1, u2elo2]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h3, h958, h968, h969, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1002_1, u2elo2]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h3, h958, h969, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1002_1, u2elo2]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1002_1, u2elo2]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h2, hlam, p1002_0]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [hlam, p1002_0]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h2, h968, h969, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1002_1]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h2, h3, h958, h969, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1002_1, u2elo2]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h2, h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1002_1, u2elo2]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h958, hlam, p1002_1]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h964, hlam, p1002_1]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [hlam, p1002_0]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h969, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1002_1, u2elo4]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h0, h3, h964, h969, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1002_1, u2elo2]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h960, hlam, p1002_0]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h966, hlam, p1002_0]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h968, hlam, p1002_0]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [hlam, p1002_0]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h969, hlam, p1002_1]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h961, hlam, p1002_0]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h967, hlam, p1002_0]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h3, h959, h961, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1002_1, u2elo2]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [h1, h3, h965, h967, h969, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1002_1, u2elo2]
                        · have p1002_0 := h1002c.1
                          have p1002_1 := h1002c.2.1
                          have p1002_2 := h1002c.2.2.1
                          have p1002_3 := h1002c.2.2.2
                          linarith only [hlam, p1002_0]
                      · linarith only [h1001, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1001, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1001, h3, h959, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1001, h3, h958, hlam, ht01, ht12, u2elo2]
                  · linarith only [h3, h960, h968, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1033 | h1033
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1034 | h1034
                    · linarith only [h1034, h3, h959, h967, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · rcases h0emin with h1036 | h1036 | h1036 | h1036 | h1036
                      · rcases h5bigk with h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [hlam, p1037_0]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h3, h958, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1037_1, u2elo2]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h3, h958, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1037_1, u2elo2]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h3, h958, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1037_1, u2elo2]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h3, h958, h965, h967, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1037_1, u2elo2]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h2, hlam, p1037_0]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [hlam, p1037_0]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h1033, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p1037_1]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h2, h3, h958, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1037_1, u2elo2]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h967, hlam, p1037_1]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h958, hlam, p1037_1]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h964, hlam, p1037_1]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [hlam, p1037_0]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1037_1, u2elo4]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h0, h3, h964, h967, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1037_1, u2elo2]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h960, hlam, p1037_0]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h966, hlam, p1037_0]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h1033, hlam, p1037_0]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [hlam, p1037_0]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h1034, hlam, p1037_1]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h961, hlam, p1037_0]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h3, h959, h961, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1037_1, u2elo2]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h1033, h1034, h3, h959, h961, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1037_1, u2elo2]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [h1034, h3, h959, h961, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1037_1, u2elo2]
                        · have p1037_0 := h1037c.1
                          have p1037_1 := h1037c.2.1
                          have p1037_2 := h1037c.2.2.1
                          have p1037_3 := h1037c.2.2.2
                          linarith only [hlam, p1037_0]
                      · linarith only [h1036, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1036, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1036, h3, h959, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1036, h3, h958, hlam, ht01, ht12, u2elo2]
                  · linarith only [h1033, h3, h960, hlam]
              · linarith only [h3, h958, h960, h962, h966, hc12, hlam, hphi, u2elo2]
            · linarith only [h3, h959, h962, h964, h965, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
          · linarith only [h3, h958, h964, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1071 | h1071
        · linarith only [h1071, h3, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1073 | h1073
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1074 | h1074
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1075 | h1075
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1076 | h1076
                · linarith only [h1076, h2, h961, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1078 | h1078
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1079 | h1079
                    · linarith only [h1079, h959, h961, hlam]
                    · rcases h0emin with h1081 | h1081 | h1081 | h1081 | h1081
                      · rcases h5bigk with h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [hlam, p1082_0]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h3, h958, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1082_1, u2elo2]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1078, h1079, h3, h958, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1082_1, u2elo2]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1079, h3, h958, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1082_1, u2elo2]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h961, hlam, p1082_1]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h2, hlam, p1082_0]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [hlam, p1082_0]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1078, h1079, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1082_1]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1079, h2, h3, h958, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1082_1, u2elo2]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1076, hlam, p1082_1]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h958, hlam, p1082_1]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1073, hlam, p1082_1]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [hlam, p1082_0]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1079, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1082_1, u2elo4]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h0, h1073, h3, h961, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1082_1, u2elo2]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h960, hlam, p1082_0]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1075, hlam, p1082_0]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1078, hlam, p1082_0]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [hlam, p1082_0]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1079, hlam, p1082_1]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1079, h960, hc34, hc45, hlam, hphi, p1082_1]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1075, h1079, hc34, hc45, hlam, hphi, p1082_1]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1078, h1079, hc34, hc45, hlam, hphi, p1082_1]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [h1079, hc34, hc45, hlam, hphi, p1082_1]
                        · have p1082_0 := h1082c.1
                          have p1082_1 := h1082c.2.1
                          have p1082_2 := h1082c.2.2.1
                          have p1082_3 := h1082c.2.2.2
                          linarith only [hlam, p1082_0]
                      · linarith only [h1081, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1081, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1081, h3, h959, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1081, h3, h958, hlam, ht01, ht12, u2elo2]
                  · linarith only [h1078, h3, h960, hlam]
              · linarith only [h1071, h1075, h3, h958, h960, hc12, hlam, hphi, u2elo2]
            · linarith only [h1071, h1073, h1074, h3, h959, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
          · linarith only [h1073, h3, h958, hc12, hlam, hphi, u2elo2]
    · linarith only [h3, h958, h960, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1117 | h1117
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1118 | h1118
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1119 | h1119
        · linarith only [h1119, h3, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1121 | h1121
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1122 | h1122
            · linarith only [h0, h1, h1121, h1122, h3, h959, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1124 | h1124
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1125 | h1125
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1126 | h1126
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1127 | h1127
                    · rcases h0emin with h1128 | h1128 | h1128 | h1128 | h1128
                      · rcases h5bigk with h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c | h1129c
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [hlam, p1129_0]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1121, h1126, h1127, h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1129_1, u2elo2]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1126, h1127, h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1129_1, u2elo2]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1127, h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1129_1, u2elo2]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1129_1, u2elo2]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h2, hlam, p1129_0]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [hlam, p1129_0]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1126, h1127, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1129_1]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1127, h2, h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1129_1, u2elo2]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h2, h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1129_1, u2elo2]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h958, hlam, p1129_1]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1121, hlam, p1129_1]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [hlam, p1129_0]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1127, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1129_1, u2elo4]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h0, h1121, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1129_1, u2elo2]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1117, hlam, p1129_0]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1124, hlam, p1129_0]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1126, hlam, p1129_0]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [hlam, p1129_0]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1117, hc03, hc45, hlam, hphi, ht0b, ht5b, p1129_1]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1118, hlam, p1129_0]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1125, hlam, p1129_0]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1118, h959, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1129_1]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [h1127, hlam, p1129_0]
                        · have p1129_0 := h1129c.1
                          have p1129_1 := h1129c.2.1
                          have p1129_2 := h1129c.2.2.1
                          have p1129_3 := h1129c.2.2.2
                          linarith only [hlam, p1129_0]
                      · linarith only [h1128, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1128, h959, hc34, hlam, ht01, ht12, ht23]
                      · rcases h5bigk with h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c | h1157c
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [hlam, p1157_0]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h3, h958, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1157_1, u2elo2]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1126, h1127, h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1157_1, u2elo2]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1127, h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1157_1, u2elo2]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1157_1, u2elo2]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h2, hlam, p1157_0]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [hlam, p1157_0]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1126, h1127, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1157_1]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1127, h2, h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1157_1, u2elo2]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h2, h3, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1157_1, u2elo2]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h958, hlam, p1157_1]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1121, hlam, p1157_1]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [hlam, p1157_0]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1127, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1157_1, u2elo4]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h0, h1121, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1157_1, u2elo2]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1117, hlam, p1157_0]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1124, hlam, p1157_0]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1126, hlam, p1157_0]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [hlam, p1157_0]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1117, h959, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1157_1]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1118, hlam, p1157_0]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1125, hlam, p1157_0]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1118, h959, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1157_1]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [h1127, hlam, p1157_0]
                        · have p1157_0 := h1157c.1
                          have p1157_1 := h1157c.2.1
                          have p1157_2 := h1157c.2.2.1
                          have p1157_3 := h1157c.2.2.2
                          linarith only [hlam, p1157_0]
                      · linarith only [h1128, h3, h958, hlam, ht01, ht12, u2elo2]
                    · linarith only [h1125, h1127, h2, h3, h958, h959, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · linarith only [h1117, h1126, h3, h959, hc02, hc34, hlam, hphi, ht23]
                · linarith only [h1118, h1119, h1121, h1122, h1125, h3, h958, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h1117, h1119, h1121, h1124, h959, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · linarith only [h1121, h3, h958, hc12, hlam, hphi, u2elo2]
      · linarith only [h1118, h3, h958, h959, hlam]
    · linarith only [h1117, h3, h958, hlam]

end R2N4
