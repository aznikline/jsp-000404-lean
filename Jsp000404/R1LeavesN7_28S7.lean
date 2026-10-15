import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_28S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s2 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  rcases m.htr 0 2 3 (by decide) (by decide) with h1965 | h1965
  · exact r1l7_10_12_25_L_I_L_R_H_I_s3 m hb0 hb2 hb5 h0 h1414 h1728 h1965
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5022 | h5022
    · linarith only [h1965, h5022, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5024 | h5024
      · linarith only [h1965, h5024, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5026 | h5026
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5027 | h5027
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5028 | h5028
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5029 | h5029
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5030 | h5030
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5031 | h5031
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5032 | h5032
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5033 | h5033
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5034 | h5034
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5035 | h5035
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5036 | h5036
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5037 | h5037
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5038 | h5038
                                · rcases h0bigk with h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c | h5039c
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [hlam, p5039_0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h0, hlam, p5039_1]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h1414, hlam, p5039_0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h0, h5024, h5028, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5039_1, u2ehi0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h1728, hlam, p5039_1]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h1965, h5029, hc01, hc12, hlam, hphi, p5039_1]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [hlam, p5039_0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h1965, hlam, p5039_0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h5022, hlam, p5039_1]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h5024, hlam, p5039_0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h1965, h5029, hc01, hc12, hlam, hphi, p5039_1]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h1965, h5029, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5039_1, u2ehi0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [hlam, p5039_0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h1965, h5022, h5029, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5039_1, u2ehi0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h1728, h1965, h5029, hc01, hc12, hlam, hphi, p5039_1]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h5022, h5029, h5035, hc01, hc12, hlam, hphi, p5039_1]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h5022, h5029, h5035, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5039_1, u2ehi0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h5026, hlam, p5039_0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [hlam, p5039_0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h5022, h5024, h5029, h5035, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5039_1, u2ehi0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h5024, h5029, h5035, h5037, hc01, hc12, hlam, hphi, p5039_1]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h5024, h5029, h5035, h5037, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5039_1, u2ehi0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h5027, hlam, p5039_0]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [h5028, hlam, p5039_1]
                                  · have p5039_0 := h5039c.1
                                    have p5039_1 := h5039c.2.1
                                    have p5039_2 := h5039c.2.2.1
                                    have p5039_3 := h5039c.2.2.2
                                    linarith only [hlam, p5039_0]
                                · rcases h0bigk with h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c | h5065c
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [hlam, p5065_0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h0, hlam, p5065_1]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h1414, hlam, p5065_0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h5028, h5038, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5065_1]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h1728, hlam, p5065_1]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h1965, h5029, hc01, hc12, hlam, hphi, p5065_1]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [hlam, p5065_0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h1965, hlam, p5065_0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h5022, hlam, p5065_1]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h5024, hlam, p5065_0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h1965, h5029, hc01, hc12, hlam, hphi, p5065_1]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h1965, h5029, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5065_1, u2ehi0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [hlam, p5065_0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h1965, h5028, h5029, h5038, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5065_1]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h1728, h1965, h5029, hc01, hc12, hlam, hphi, p5065_1]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h5022, h5029, h5035, hc01, hc12, hlam, hphi, p5065_1]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h5022, h5029, h5035, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5065_1, u2ehi0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h5026, hlam, p5065_0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [hlam, p5065_0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h5022, h5024, h5029, h5035, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5065_1, u2ehi0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h5024, h5029, h5035, h5037, hc01, hc12, hlam, hphi, p5065_1]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h5024, h5029, h5035, h5037, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5065_1, u2ehi0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h5027, hlam, p5065_0]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [h5028, hlam, p5065_1]
                                  · have p5065_0 := h5065c.1
                                    have p5065_1 := h5065c.2.1
                                    have p5065_2 := h5065c.2.2.1
                                    have p5065_3 := h5065c.2.2.2
                                    linarith only [hlam, p5065_0]
                              · linarith only [h5022, h5037, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                            · linarith only [h1965, h5036, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1965, h5035, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1965, h5026, h5028, h5029, h5030, h5034, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1414, h5027, h5033, hlam]
                    · linarith only [h1965, h5029, h5032, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1965, h5029, h5031, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1965, h5029, h5030, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5099 | h5099
                · linarith only [h5029, h5099, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5101 | h5101
                  · linarith only [h5029, h5101, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5103 | h5103
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5104 | h5104
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5105 | h5105
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5106 | h5106
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5107 | h5107
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5108 | h5108
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5109 | h5109
                                · rcases h0bigk with h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [hlam, p5110_0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h0, hlam, p5110_1]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h1414, hlam, p5110_0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h0, h5101, h5106, h5108, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5110_1]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h1728, hlam, p5110_1]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h0, h5101, h5106, h5108, hc01, hc23, hlam, hphi, ht12, p5110_1]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [hlam, p5110_0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h1965, hlam, p5110_0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h5022, hlam, p5110_1]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h5024, hlam, p5110_0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    rcases p5110_3 (m.d 0 1) (by simp) with h5121 | h5121
                                    · linarith only [h1414, h5121, hlam]
                                    · rcases p5110_3 (m.d 0 2) (by simp) with h5123 | h5123
                                      · linarith only [h1965, h5123, hlam]
                                      · linarith only [h0, h5123, hlam]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h1965, hc23, hlam, hphi, p5110_1, u2ehi0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [hlam, p5110_0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h1965, h5022, hc23, hlam, hphi, p5110_1, u2ehi0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h1965, h5024, hc23, hlam, hphi, p5110_1, u2ehi0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    rcases p5110_3 (m.d 0 1) (by simp) with h5130 | h5130
                                    · linarith only [h5130, hlam, p5110_0]
                                    · rcases p5110_3 (m.d 0 2) (by simp) with h5132 | h5132
                                      · linarith only [h5022, h5132, hlam]
                                      · linarith only [h0, h5132, hlam]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h5022, h5106, hc23, hlam, hphi, p5110_1, u2ehi0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h5026, hlam, p5110_0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [hlam, p5110_0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h1414, h5024, h5026, h5029, hc23, hlam, hphi, p5110_1, u2ehi0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    rcases p5110_3 (m.d 0 1) (by simp) with h5139 | h5139
                                    · linarith only [h1728, h5139, hlam]
                                    · rcases p5110_3 (m.d 0 2) (by simp) with h5141 | h5141
                                      · linarith only [h5024, h5141, hlam]
                                      · linarith only [h0, h5141, hlam]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h5024, h5106, h5108, hc23, hlam, hphi, p5110_1, u2ehi0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h5027, hlam, p5110_0]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [h5028, hlam, p5110_1]
                                  · have p5110_0 := h5110c.1
                                    have p5110_1 := h5110c.2.1
                                    have p5110_2 := h5110c.2.2.1
                                    have p5110_3 := h5110c.2.2.2
                                    linarith only [hlam, p5110_0]
                                · rcases h0bigk with h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [hlam, p5148_0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h0, hlam, p5148_1]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h1414, hlam, p5148_0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h0, h5101, h5106, h5108, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5148_1]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h1728, hlam, p5148_1]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h0, h5101, h5106, h5108, hc01, hc23, hlam, hphi, ht12, p5148_1]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [hlam, p5148_0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h1965, hlam, p5148_0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h5022, hlam, p5148_1]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h5024, hlam, p5148_0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    rcases p5148_3 (m.d 0 1) (by simp) with h5159 | h5159
                                    · linarith only [h1414, h5159, hlam]
                                    · rcases p5148_3 (m.d 0 2) (by simp) with h5161 | h5161
                                      · linarith only [h1965, h5161, hlam]
                                      · linarith only [h0, h5161, hlam]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h1414, h5029, hc23, hlam, hphi, p5148_1, u2ehi0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [hlam, p5148_0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h1414, h5024, h5028, h5029, hc23, hlam, hphi, p5148_1, u2ehi0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h1414, h5024, h5029, hc23, hlam, hphi, p5148_1, u2ehi0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    rcases p5148_3 (m.d 0 1) (by simp) with h5168 | h5168
                                    · linarith only [h5168, hlam, p5148_0]
                                    · rcases p5148_3 (m.d 0 2) (by simp) with h5170 | h5170
                                      · linarith only [h5022, h5170, hlam]
                                      · linarith only [h0, h5170, hlam]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h5022, h5106, hc23, hlam, hphi, p5148_1, u2ehi0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h5026, hlam, p5148_0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [hlam, p5148_0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h1414, h5024, h5026, h5029, hc23, hlam, hphi, p5148_1, u2ehi0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    rcases p5148_3 (m.d 0 1) (by simp) with h5177 | h5177
                                    · linarith only [h1728, h5177, hlam]
                                    · rcases p5148_3 (m.d 0 2) (by simp) with h5179 | h5179
                                      · linarith only [h5024, h5179, hlam]
                                      · linarith only [h0, h5179, hlam]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h5024, h5106, h5108, hc23, hlam, hphi, p5148_1, u2ehi0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h5027, hlam, p5148_0]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [h5028, hlam, p5148_1]
                                  · have p5148_0 := h5148c.1
                                    have p5148_1 := h5148c.2.1
                                    have p5148_2 := h5148c.2.2.1
                                    have p5148_3 := h5148c.2.2.2
                                    linarith only [hlam, p5148_0]
                              · linarith only [h5022, h5108, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                            · linarith only [h1965, h5107, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1965, h5106, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h0, h1414, h5026, h5028, h5099, h5105, hc01, hc13, hlam, hphi]
                      · linarith only [h1414, h5027, h5104, hlam]
                    · linarith only [h1414, h5026, h5103, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5192 | h5192
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5193 | h5193
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5194 | h5194
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5195 | h5195
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5196 | h5196
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5197 | h5197
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5198 | h5198
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5199 | h5199
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5200 | h5200
                              · linarith only [h5022, h5028, h5200, hc24, hlam, hphi, u2ehi0]
                              · linarith only [h5022, h5192, h5195, h5197, h5200, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · linarith only [h1965, h5027, h5199, hlam]
                          · linarith only [h1965, h5026, h5027, h5028, h5192, h5195, h5197, h5198, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h5022, h5193, h5197, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1414, h5027, h5196, hlam]
                    · linarith only [h1414, h5026, h5195, hlam]
                  · linarith only [h5192, h5194, hc25, hlam, hphi, u2ehi2]
                · linarith only [h1965, h5192, h5193, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5210 | h5210
                · linarith only [h5192, h5210, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5212 | h5212
                  · linarith only [h5192, h5212, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5214 | h5214
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5215 | h5215
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5216 | h5216
                        · linarith only [h5022, h5028, h5210, h5216, hc24, hlam, hphi, u2ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5218 | h5218
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5219 | h5219
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5220 | h5220
                              · linarith only [h0, h5210, h5216, h5218, h5220, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h5022, h5220, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                            · linarith only [h1414, h5027, h5192, h5219, hlam]
                          · linarith only [h1965, h5218, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1414, h5027, h5215, hlam]
                    · linarith only [h1414, h5026, h5028, h5214, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5227 | h5227
            · linarith only [h5026, h5027, h5227, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5229 | h5229
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5230 | h5230
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5231 | h5231
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5232 | h5232
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5233 | h5233
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5234 | h5234
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5235 | h5235
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5236 | h5236
                            · linarith only [h5022, h5026, h5027, h5229, h5236, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · linarith only [h1965, h5233, h5236, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1965, h5026, h5235, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h5022, h5230, h5234, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1965, h5229, h5233, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1965, h5026, h5027, h5229, h5232, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1965, h5229, h5231, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1965, h5229, h5230, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5245 | h5245
                · linarith only [h5229, h5245, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5247 | h5247
                  · linarith only [h5229, h5247, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5249 | h5249
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5250 | h5250
                      · linarith only [h1965, h5027, h5229, h5250, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5252 | h5252
                        · linarith only [h5022, h5227, h5249, h5250, h5252, hc35, hlam, hphi, ht23, u2ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5254 | h5254
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5255 | h5255
                            · linarith only [h5245, h5249, h5250, h5255, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h1965, h5255, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h0, h5026, h5229, h5254, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h5026, h5027, h5249, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5260 | h5260
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5261 | h5261
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5262 | h5262
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5263 | h5263
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5264 | h5264
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5265 | h5265
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5266 | h5266
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5267 | h5267
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5268 | h5268
                          · linarith only [h5026, h5260, h5262, h5268, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h1965, h5265, h5268, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h5022, h5024, h5026, h5260, h5261, h5265, h5267, hc24, hlam, hphi, u2ehi0]
                      · linarith only [h5026, h5260, h5266, hc13, hc34, hlam, hphi]
                    · linarith only [h1965, h5262, h5265, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h5263, h5264, hc25, hlam, hphi, u2ehi3]
                · linarith only [h1965, h5262, h5263, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5276 | h5276
                · linarith only [h5262, h5276, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5278 | h5278
                  · linarith only [h5262, h5278, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5280 | h5280
                    · linarith only [h1965, h5026, h5262, h5280, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5282 | h5282
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5283 | h5283
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5284 | h5284
                          · linarith only [h1414, h5024, h5260, h5280, h5284, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h1965, h5284, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1414, h5024, h5026, h5260, h5261, h5280, h5283, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1414, h5260, h5282, hlam]
            · linarith only [h5026, h5260, h5261, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5290 | h5290
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5291 | h5291
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5292 | h5292
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5293 | h5293
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5294 | h5294
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5295 | h5295
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5296 | h5296
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5297 | h5297
                          · linarith only [h1965, h5026, h5297, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h1965, h5291, h5294, h5297, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h5022, h5290, h5292, h5296, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h5026, h5294, h5295, hc03, hc35, hlam, hphi]
                    · linarith only [h1965, h5291, h5294, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1965, h5291, h5293, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1965, h5291, h5292, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5305 | h5305
                · linarith only [h5291, h5305, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5307 | h5307
                  · linarith only [h5291, h5307, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5309 | h5309
                    · linarith only [h1965, h5026, h5291, h5309, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5311 | h5311
                      · linarith only [h1965, h5260, h5309, h5311, hc34, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5313 | h5313
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5314 | h5314
                          · linarith only [h5291, h5309, h5314, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h1965, h5314, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h0, h5026, h5290, h5305, h5313, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5318 | h5318
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5319 | h5319
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5320 | h5320
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5321 | h5321
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5322 | h5322
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5323 | h5323
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5324 | h5324
                          · linarith only [h1965, h5026, h5318, h5324, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1965, h5324, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h5022, h5319, h5323, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1965, h5026, h5321, h5322, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1965, h5318, h5321, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1965, h5318, h5320, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1965, h5318, h5319, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5332 | h5332
                · linarith only [h5318, h5332, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5334 | h5334
                  · linarith only [h5318, h5334, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5336 | h5336
                    · linarith only [h1965, h5026, h5318, h5336, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5338 | h5338
                      · linarith only [h1965, h5260, h5336, h5338, hc34, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5340 | h5340
                        · linarith only [h1965, h5026, h5290, h5332, h5340, hc24, hlam, hphi, u2ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5342 | h5342
                          · linarith only [h1965, h5026, h5342, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h1965, h5342, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 7234000 in
set_option maxHeartbeats 7234000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  rcases m.htr 0 1 5 (by decide) (by decide) with h1728 | h1728
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1729 | h1729
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1730 | h1730
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1731 | h1731
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1732 | h1732
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1733 | h1733
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1734 | h1734
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1735 | h1735
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1736 | h1736
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1737 | h1737
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1738 | h1738
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1739 | h1739
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1740 | h1740
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1741 | h1741
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1742 | h1742
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1743 | h1743
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1744 | h1744
                                  · rcases h0bigk with h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [hlam, p1745_0]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h0, hlam, p1745_1]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1414, hlam, p1745_0]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1414, h1730, h1735, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1745_1, u2ehi3]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1414, h1728, h1735, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1745_1, u2ehi4]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h0, h1728, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1745_1, u2ehi4]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [hlam, p1745_0]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h0, h1414, h1728, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1745_1, u2ehi4]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      rcases p1745_3 (m.d 0 1) (by simp) with h1754 | h1754
                                      · linarith only [h0, h1754, hlam]
                                      · linarith only [h0, h1728, h1737, h1754, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1745_1, u2ehi4]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      rcases p1745_3 (m.d 0 1) (by simp) with h1757 | h1757
                                      · linarith only [h0, h1757, hlam]
                                      · linarith only [h1728, h1757, hlam]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1728, h1737, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1745_1, u2ehi4]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1729, hlam, p1745_1]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [hlam, p1745_0]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      rcases p1745_3 (m.d 0 1) (by simp) with h1763 | h1763
                                      · linarith only [h1414, h1763, hlam]
                                      · linarith only [h1414, h1728, h1735, h1737, h1763, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1745_1, u2ehi4]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      rcases p1745_3 (m.d 0 1) (by simp) with h1766 | h1766
                                      · linarith only [h1414, h1766, hlam]
                                      · linarith only [h1728, h1766, hlam]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1728, h1737, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1745_1, u2ehi4]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1730, hlam, p1745_0]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1732, hlam, p1745_0]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [hlam, p1745_0]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      rcases p1745_3 (m.d 0 1) (by simp) with h1773 | h1773
                                      · linarith only [h0, h1728, h1737, h1773, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1745_1, u2ehi4]
                                      · linarith only [h1728, h1773, hlam]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1728, hlam, p1745_0]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1731, hlam, p1745_1]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1733, hlam, p1745_0]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [h1734, hlam, p1745_1]
                                    · have p1745_0 := h1745c.1
                                      have p1745_1 := h1745c.2.1
                                      have p1745_2 := h1745c.2.2.1
                                      have p1745_3 := h1745c.2.2.2
                                      linarith only [hlam, p1745_0]
                                  · rcases h0bigk with h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [hlam, p1781_0]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h0, hlam, p1781_1]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1414, hlam, p1781_0]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1414, h1730, h1735, h1743, h1744, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1781_1]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1414, h1728, h1735, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1781_1, u2ehi4]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h0, h1728, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1781_1, u2ehi4]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [hlam, p1781_0]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h0, h1414, h1728, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1781_1, u2ehi4]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h0, h1730, h1743, h1744, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1781_1]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      rcases p1781_3 (m.d 0 1) (by simp) with h1791 | h1791
                                      · linarith only [h0, h1791, hlam]
                                      · linarith only [h1728, h1791, hlam]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1728, h1737, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1781_1, u2ehi4]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1729, hlam, p1781_1]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [hlam, p1781_0]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1414, h1730, h1735, h1743, h1744, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1781_1]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      rcases p1781_3 (m.d 0 1) (by simp) with h1798 | h1798
                                      · linarith only [h1414, h1798, hlam]
                                      · linarith only [h1728, h1798, hlam]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1728, h1737, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1781_1, u2ehi4]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1730, hlam, p1781_0]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1732, hlam, p1781_0]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [hlam, p1781_0]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      rcases p1781_3 (m.d 0 1) (by simp) with h1805 | h1805
                                      · linarith only [h1414, h1728, h1735, h1737, h1805, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1781_1, u2ehi4]
                                      · linarith only [h1728, h1805, hlam]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1728, hlam, p1781_0]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1731, hlam, p1781_1]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1733, hlam, p1781_0]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [h1734, hlam, p1781_1]
                                    · have p1781_0 := h1781c.1
                                      have p1781_1 := h1781c.2.1
                                      have p1781_2 := h1781c.2.2.1
                                      have p1781_3 := h1781c.2.2.2
                                      linarith only [hlam, p1781_0]
                                · linarith only [h1414, h1728, h1735, h1740, h1743, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h1414, h1728, h1735, h1739, h1741, h1742, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1815 | h1815
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1816 | h1816
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1817 | h1817
                                  · rcases h0bigk with h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c | h1818c
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [hlam, p1818_0]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h0, hlam, p1818_1]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1414, hlam, p1818_0]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1414, h1730, h1735, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1818_1, u2ehi3]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1414, h1731, h1735, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1818_1, u2ehi4]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h0, h1728, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1818_1, u2ehi4]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [hlam, p1818_0]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h0, h1414, h1728, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1818_1, u2ehi4]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h0, h1732, h1741, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1818_1, u2ehi2]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      rcases p1818_3 (m.d 0 1) (by simp) with h1828 | h1828
                                      · linarith only [h0, h1828, hlam]
                                      · linarith only [h1728, h1828, hlam]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1728, h1737, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1818_1, u2ehi4]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1729, hlam, p1818_1]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [hlam, p1818_0]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1414, h1732, h1735, h1741, h1815, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1818_1, u2ehi4]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      rcases p1818_3 (m.d 0 1) (by simp) with h1835 | h1835
                                      · linarith only [h1414, h1835, hlam]
                                      · linarith only [h1728, h1835, hlam]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1728, h1737, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1818_1, u2ehi4]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1730, hlam, p1818_0]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1732, hlam, p1818_0]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [hlam, p1818_0]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      rcases p1818_3 (m.d 0 1) (by simp) with h1842 | h1842
                                      · linarith only [h1414, h1728, h1735, h1737, h1842, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1818_1, u2ehi4]
                                      · linarith only [h1728, h1842, hlam]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1728, hlam, p1818_0]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1731, hlam, p1818_1]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1733, hlam, p1818_0]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [h1734, hlam, p1818_1]
                                    · have p1818_0 := h1818c.1
                                      have p1818_1 := h1818c.2.1
                                      have p1818_2 := h1818c.2.2.1
                                      have p1818_3 := h1818c.2.2.2
                                      linarith only [hlam, p1818_0]
                                  · linarith only [h1741, h1815, h1817, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                · linarith only [h1414, h1728, h1735, h1740, h1741, h1815, h1816, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                              · linarith only [h1414, h1728, h1735, h1739, h1815, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1853 | h1853
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1854 | h1854
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1855 | h1855
                                · linarith only [h1736, h1740, h1855, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1857 | h1857
                                  · linarith only [h1736, h1740, h1853, h1857, hlam]
                                  · rcases h0bigk with h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h0, hlam, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1414, hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1414, h1734, h1735, h1736, h1740, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1859_1, u2ehi3]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1414, h1734, h1735, h1736, h1740, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1859_1, u2ehi3]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h0, h1728, h1734, h1736, h1740, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1859_1, u2ehi3]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h0, h1414, h1728, h1734, h1736, h1740, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1859_1, u2ehi3]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h0, h1734, h1736, h1740, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1859_1, u2ehi3]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h0, h1734, h1736, h1740, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1859_1, u2ehi3]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1728, h1734, h1736, h1740, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1859_1, u2ehi3]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1729, hlam, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1414, h1734, h1735, h1736, h1740, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1859_1, u2ehi3]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1414, h1734, h1735, h1736, h1740, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1859_1, u2ehi3]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1728, h1734, h1736, h1740, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1859_1, u2ehi3]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1730, hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1732, hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1414, h1732, h1734, h1735, h1736, h1740, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1859_1, u2ehi3]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1728, hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1731, hlam, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1733, hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1734, hlam, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [hlam, p1859_0]
                              · linarith only [h0, h1728, h1739, h1854, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h1738, h1740, h1853, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h1414, h1728, h1731, h1739, hc35, hlam, hphi, ht23, u2ehi4]
                      · linarith only [h1414, h1728, h1729, h1732, h1737, h1738, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h0, h1728, h1731, h1737, hlam]
                  · linarith only [h0, h1730, h1736, hlam]
                · linarith only [h0, h1730, h1735, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1892 | h1892
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1893 | h1893
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1894 | h1894
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1895 | h1895
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1896 | h1896
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1897 | h1897
                          · linarith only [h1414, h1728, h1730, h1734, h1892, h1897, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1899 | h1899
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1900 | h1900
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1901 | h1901
                                · linarith only [h1730, h1734, h1901, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1903 | h1903
                                  · linarith only [h1729, h1730, h1734, h1899, h1903, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · rcases h0bigk with h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [hlam, p1905_0]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h0, hlam, p1905_1]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1414, hlam, p1905_0]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1414, h1730, h1892, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1905_1, u2ehi3]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1414, h1728, h1892, h1894, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1905_1, u2ehi4]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h0, h1728, h1894, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1905_1, u2ehi4]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [hlam, p1905_0]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h0, h1414, h1728, h1894, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1905_1, u2ehi4]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      rcases p1905_3 (m.d 0 1) (by simp) with h1914 | h1914
                                      · linarith only [h0, h1914, hlam]
                                      · linarith only [h1728, h1734, h1893, h1897, h1914, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      rcases p1905_3 (m.d 0 1) (by simp) with h1917 | h1917
                                      · linarith only [h0, h1917, hlam]
                                      · linarith only [h1728, h1917, hlam]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1728, h1893, h1897, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1905_1, u2ehi3]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1729, hlam, p1905_1]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [hlam, p1905_0]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      rcases p1905_3 (m.d 0 1) (by simp) with h1923 | h1923
                                      · linarith only [h1414, h1923, hlam]
                                      · linarith only [h1728, h1734, h1923, hlam]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      rcases p1905_3 (m.d 0 1) (by simp) with h1926 | h1926
                                      · linarith only [h1414, h1926, hlam]
                                      · linarith only [h1728, h1926, hlam]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1728, h1893, h1897, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1905_1, u2ehi3]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1730, hlam, p1905_0]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1732, hlam, p1905_0]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [hlam, p1905_0]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1734, hlam, p1905_0]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1728, hlam, p1905_0]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1731, hlam, p1905_1]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1733, hlam, p1905_0]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [h1414, h1728, h1730, h1892, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1905_1, u2ehi3]
                                    · have p1905_0 := h1905c.1
                                      have p1905_1 := h1905c.2.1
                                      have p1905_2 := h1905c.2.2.1
                                      have p1905_3 := h1905c.2.2.2
                                      linarith only [hlam, p1905_0]
                              · linarith only [h1414, h1728, h1892, h1896, h1900, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h1732, h1734, h1899, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h1414, h1728, h1731, h1896, hc35, hlam, hphi, ht23, u2ehi4]
                      · linarith only [h1414, h1728, h1732, h1894, h1895, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h0, h1729, h1894, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h1414, h1728, h1730, h1734, h1892, h1893, hlam]
                · linarith only [h0, h1729, h1892, hlam]
            · linarith only [h1414, h1728, h1733, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1947 | h1947
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1948 | h1948
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1949 | h1949
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1950 | h1950
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1951 | h1951
                    · linarith only [h1414, h1728, h1732, h1951, hc34, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h0, h1729, h1951, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1730, h1950, hlam]
                · linarith only [h0, h1729, h1949, hlam]
              · linarith only [h1414, h1728, h1732, h1948, hlam]
            · linarith only [h1414, h1728, h1947, hlam]
        · linarith only [h1729, h1731, hc25, hlam, hphi, u2ehi2]
      · linarith only [h1729, h1730, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1960 | h1960
      · linarith only [h1729, h1960, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1962 | h1962
        · linarith only [h1729, h1962, hc23, hlam, hphi, u2ehi4]
        · linarith only [h0, h1728, h1962, hlam]
  · exact r1l7_10_12_25_L_I_L_R_H_I_s2 m hb0 hb2 hb5 h0 h1414 h1728

set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1414 | h1414
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1415 | h1415
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1416 | h1416
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1417 | h1417
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1418 | h1418
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1419 | h1419
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1420 | h1420
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1421 | h1421
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1422 | h1422
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1423 | h1423
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1424 | h1424
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1425 | h1425
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1426 | h1426
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1427 | h1427
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1428 | h1428
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1429 | h1429
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1430 | h1430
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1431 | h1431
                                    · linarith only [h0, h1414, h1422, h1428, h1431, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h0, h1414, h1425, h1427, h1431, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h0, h1414, h1425, h1427, h1430, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h1414, h1420, h1429, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h1414, h1419, h1428, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h1414, h1419, h1421, h1423, h1427, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h0, h1414, h1420, h1425, h1426, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1414, h1419, h1422, h1425, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h1414, h1422, h1424, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1418, h1423, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h1414, h1418, h1419, h1421, h1422, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1443 | h1443
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1444 | h1444
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1445 | h1445
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1446 | h1446
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1447 | h1447
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1448 | h1448
                            · linarith only [h0, h1414, h1417, h1421, h1446, h1448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1450 | h1450
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1451 | h1451
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1452 | h1452
                                  · linarith only [h1417, h1421, h1452, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1454 | h1454
                                    · linarith only [h0, h1414, h1421, h1443, h1450, h1454, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c | h1456c
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [hlam, p1456_0]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h0, hlam, p1456_1]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h0, h1414, h1443, h1451, h1454, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1456_1]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h0, h1417, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1456_1, u2ehi3]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h0, h1415, h1444, h1448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1456_1, u2ehi3]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h1414, h1444, h1447, h1448, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1456_1, u2ehi3]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [hlam, p1456_0]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        rcases p1456_3 (m.d 0 1) (by simp) with h1464 | h1464
                                        · linarith only [h0, h1464, hlam]
                                        · linarith only [h1414, h1464, hlam]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        rcases p1456_3 (m.d 0 1) (by simp) with h1467 | h1467
                                        · linarith only [h0, h1467, hlam]
                                        · linarith only [h1414, h1421, h1444, h1447, h1448, h1467, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        rcases p1456_3 (m.d 0 1) (by simp) with h1470 | h1470
                                        · linarith only [h0, h1470, hlam]
                                        · linarith only [h1415, h1470, hlam]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h1414, hlam, p1456_1]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h1416, hlam, p1456_1]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [hlam, p1456_0]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h0, h1414, h1417, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1456_1, u2ehi3]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h0, h1414, h1415, h1444, h1448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1456_1, u2ehi3]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h1414, h1444, h1447, h1448, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1456_1, u2ehi3]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h1417, hlam, p1456_0]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h1419, hlam, p1456_0]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [hlam, p1456_0]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h1421, hlam, p1456_0]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h1415, hlam, p1456_0]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h1418, hlam, p1456_1]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h1420, hlam, p1456_0]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [h0, h1415, h1417, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1456_1, u2ehi3]
                                      · have p1456_0 := h1456c.1
                                        have p1456_1 := h1456c.2.1
                                        have p1456_2 := h1456c.2.2.1
                                        have p1456_3 := h1456c.2.2.2
                                        linarith only [hlam, p1456_0]
                                · linarith only [h0, h1414, h1420, h1451, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h1414, h1419, h1450, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h1414, h1420, h1446, h1447, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1414, h1419, h1443, h1446, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h1414, h1443, h1445, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1414, h1417, h1420, h1421, h1443, h1444, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h1418, h1443, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1495 | h1495
                · linarith only [h1419, h1420, h1495, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1497 | h1497
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1498 | h1498
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1499 | h1499
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1500 | h1500
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1501 | h1501
                          · linarith only [h1414, h1420, h1501, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1503 | h1503
                            · linarith only [h0, h1415, h1417, h1495, h1500, h1501, h1503, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1505 | h1505
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1506 | h1506
                                · linarith only [h1414, h1420, h1497, h1506, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1508 | h1508
                                  · linarith only [h1417, h1495, h1508, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1510 | h1510
                                    · linarith only [h0, h1415, h1495, h1497, h1501, h1505, h1510, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [hlam, p1512_0]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h0, hlam, p1512_1]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h0, h1414, h1497, h1505, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1512_1]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h0, h1417, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1512_1, u2ehi3]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h0, h1418, h1505, h1506, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1512_1, u2ehi3]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h0, h1414, h1498, h1500, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1512_1, u2ehi3]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [hlam, p1512_0]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        rcases p1512_3 (m.d 0 1) (by simp) with h1520 | h1520
                                        · linarith only [h0, h1520, hlam]
                                        · linarith only [h1414, h1520, hlam]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        rcases p1512_3 (m.d 0 1) (by simp) with h1523 | h1523
                                        · linarith only [h0, h1523, hlam]
                                        · linarith only [h0, h1415, h1499, h1505, h1506, h1523, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1512_1, u2ehi3]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        rcases p1512_3 (m.d 0 1) (by simp) with h1526 | h1526
                                        · linarith only [h0, h1526, hlam]
                                        · linarith only [h1415, h1526, hlam]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h1414, hlam, p1512_1]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h1416, hlam, p1512_1]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [hlam, p1512_0]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h0, h1414, h1417, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1512_1, u2ehi3]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h1420, hlam, p1512_1]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h1414, h1498, h1500, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1512_1, u2ehi3]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h1417, hlam, p1512_0]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h1419, hlam, p1512_0]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [hlam, p1512_0]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h1495, hlam, p1512_0]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h1415, hlam, p1512_0]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h1418, hlam, p1512_1]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h0, h1414, h1415, h1498, h1500, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1512_1, u2ehi3]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [h0, h1415, h1417, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1512_1, u2ehi3]
                                      · have p1512_0 := h1512c.1
                                        have p1512_1 := h1512c.2.1
                                        have p1512_2 := h1512c.2.2.1
                                        have p1512_3 := h1512c.2.2.2
                                        linarith only [hlam, p1512_0]
                              · linarith only [h0, h1414, h1419, h1505, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1419, h1420, h1500, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h1414, h1497, h1499, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1414, h1417, h1497, h1498, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h1415, h1418, h1497, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1549 | h1549
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1550 | h1550
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1551 | h1551
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1552 | h1552
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1553 | h1553
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1554 | h1554
                        · linarith only [h0, h1414, h1419, h1554, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1556 | h1556
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1557 | h1557
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1558 | h1558
                              · linarith only [h0, h1414, h1417, h1419, h1551, h1558, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1560 | h1560
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1561 | h1561
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1562 | h1562
                                    · rcases h0bigk with h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [hlam, p1563_0]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h0, hlam, p1563_1]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h0, h1414, h1551, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1563_1, u2ehi2]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h0, h1415, h1419, h1549, h1553, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1563_1, u2ehi4]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h0, h1415, h1553, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1563_1, u2ehi4]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h0, h1414, h1553, h1556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1563_1, u2ehi4]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [hlam, p1563_0]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        rcases p1563_3 (m.d 0 1) (by simp) with h1571 | h1571
                                        · linarith only [h0, h1571, hlam]
                                        · linarith only [h1414, h1571, hlam]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        rcases p1563_3 (m.d 0 1) (by simp) with h1574 | h1574
                                        · linarith only [h0, h1574, hlam]
                                        · linarith only [h0, h1414, h1553, h1556, h1574, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1563_1, u2ehi4]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        rcases p1563_3 (m.d 0 1) (by simp) with h1577 | h1577
                                        · linarith only [h0, h1577, hlam]
                                        · linarith only [h1415, h1577, hlam]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1414, hlam, p1563_1]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1416, hlam, p1563_1]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [hlam, p1563_0]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1419, hlam, p1563_1]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1415, h1419, h1553, hc34, hlam, hphi, ht23, p1563_1, u2ehi4]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1414, h1419, h1553, h1556, hc34, hlam, hphi, ht23, p1563_1, u2ehi4]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1417, hlam, p1563_0]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1414, h1419, h1553, h1556, hc34, hlam, hphi, ht23, p1563_1, u2ehi4]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [hlam, p1563_0]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1415, h1419, h1553, hc34, hlam, hphi, ht23, p1563_1, u2ehi4]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1415, hlam, p1563_0]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1418, hlam, p1563_1]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1549, hlam, p1563_0]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [h1550, hlam, p1563_1]
                                      · have p1563_0 := h1563c.1
                                        have p1563_1 := h1563c.2.1
                                        have p1563_2 := h1563c.2.2.1
                                        have p1563_3 := h1563c.2.2.2
                                        linarith only [hlam, p1563_0]
                                    · linarith only [h1414, h1419, h1553, h1556, h1562, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                  · linarith only [h1419, h1550, h1558, h1560, h1561, hc34, hlam, hphi, ht23, u2ehi4]
                                · linarith only [h0, h1414, h1549, h1560, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h1419, h1549, h1550, h1552, h1557, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1419, h1549, h1556, hc13, hc34, hlam, hphi]
                      · linarith only [h0, h1414, h1551, h1553, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1414, h1551, h1552, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1417, h1551, hc23, hlam, hphi, u2ehi3]
                · linarith only [h1419, h1549, h1550, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1604 | h1604
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1605 | h1605
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1606 | h1606
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1607 | h1607
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1608 | h1608
                        · linarith only [h0, h1414, h1419, h1608, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1610 | h1610
                          · linarith only [h1414, h1549, h1610, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1612 | h1612
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1613 | h1613
                              · linarith only [h1414, h1419, h1605, h1613, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1615 | h1615
                                · linarith only [h1414, h1549, h1605, h1615, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1617 | h1617
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1618 | h1618
                                    · rcases h0bigk with h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [hlam, p1619_0]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h0, hlam, p1619_1]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h0, h1414, h1605, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1619_1, u2ehi2]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h0, h1417, h1615, h1617, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1619_1, u2ehi2]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h0, h1418, h1615, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1619_1, u2ehi2]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h0, h1414, h1605, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1619_1, u2ehi2]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [hlam, p1619_0]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        rcases p1619_3 (m.d 0 1) (by simp) with h1627 | h1627
                                        · linarith only [h0, h1627, hlam]
                                        · linarith only [h1414, h1627, hlam]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        rcases p1619_3 (m.d 0 1) (by simp) with h1630 | h1630
                                        · linarith only [h0, h1630, hlam]
                                        · linarith only [h0, h1415, h1607, h1615, h1630, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1619_1, u2ehi2]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        rcases p1619_3 (m.d 0 1) (by simp) with h1633 | h1633
                                        · linarith only [h0, h1633, hlam]
                                        · linarith only [h1415, h1633, hlam]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h1414, hlam, p1619_1]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h1416, hlam, p1619_1]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [hlam, p1619_0]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h1419, hlam, p1619_1]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h1549, hlam, p1619_1]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h1415, h1607, h1615, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1619_1, u2ehi2]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h1417, hlam, p1619_0]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h1414, h1419, h1605, hc34, hlam, hphi, ht23, p1619_1, u2ehi2]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [hlam, p1619_0]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h1414, h1419, h1549, h1605, hc34, hlam, hphi, ht23, p1619_1, u2ehi2]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h1415, hlam, p1619_0]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h1418, hlam, p1619_1]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h0, h1414, h1415, h1605, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1619_1, u2ehi2]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [h1604, hlam, p1619_1]
                                      · have p1619_0 := h1619c.1
                                        have p1619_1 := h1619c.2.1
                                        have p1619_2 := h1619c.2.2.1
                                        have p1619_3 := h1619c.2.2.2
                                        linarith only [hlam, p1619_0]
                                    · linarith only [h1417, h1419, h1617, h1618, hlam]
                                  · linarith only [h1419, h1604, h1613, h1617, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h1419, h1604, h1606, h1612, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h1414, h1605, h1607, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1415, h1418, h1606, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h1415, h1416, h1549, h1605, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1657 | h1657
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1658 | h1658
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1659 | h1659
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1660 | h1660
                        · linarith only [h1414, h1419, h1660, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1662 | h1662
                          · linarith only [h1414, h1549, h1662, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1664 | h1664
                            · linarith only [h1414, h1419, h1604, h1657, h1660, h1664, hc34, hlam, hphi, ht23, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1666 | h1666
                              · linarith only [h1414, h1419, h1657, h1666, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1668 | h1668
                                · linarith only [h1414, h1549, h1657, h1668, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1670 | h1670
                                  · linarith only [h1414, h1415, h1419, h1604, h1657, h1658, h1664, h1670, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1672 | h1672
                                    · linarith only [h1414, h1419, h1604, h1657, h1672, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h1414, h1419, h1657, h1672, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h1414, h1657, h1659, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1414, h1417, h1657, h1658, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h1415, h1418, h1657, hc23, hlam, hphi, u2ehi4]
          · linarith only [h1417, h1418, hc25, hlam, hphi, u2ehi3]
        · linarith only [h1416, h1417, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h1414, h1416, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1681 | h1681
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1682 | h1682
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1683 | h1683
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1684 | h1684
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1685 | h1685
              · linarith only [h1414, h1415, h1685, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1687 | h1687
                · linarith only [h1414, h1415, h1684, h1687, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1689 | h1689
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1690 | h1690
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1691 | h1691
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1692 | h1692
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1693 | h1693
                          · linarith only [h1414, h1415, h1685, h1691, h1693, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h1414, h1415, h1690, h1692, h1693, hc35, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h1684, h1685, h1692, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h1683, h1691, hlam]
                    · linarith only [h0, h1414, h1689, h1690, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1414, h1682, h1684, h1689, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1700 | h1700
              · linarith only [h1414, h1415, h1700, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1702 | h1702
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1703 | h1703
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1704 | h1704
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1705 | h1705
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1706 | h1706
                        · linarith only [h1414, h1415, h1684, h1706, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1708 | h1708
                          · linarith only [h1414, h1415, h1700, h1708, hlam]
                          · linarith only [h1414, h1415, h1703, h1708, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h1682, h1705, hc25, hlam, hphi, u2ehi3]
                    · linarith only [h0, h1414, h1682, h1703, h1704, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h1682, h1703, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1714 | h1714
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1715 | h1715
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1716 | h1716
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1717 | h1717
                        · linarith only [h1414, h1415, h1684, h1716, h1717, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1719 | h1719
                          · linarith only [h1414, h1700, h1719, hlam]
                          · linarith only [h1414, h1415, h1714, h1719, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h1414, h1714, h1716, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1414, h1714, h1715, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1682, h1714, hc23, hlam, hphi, u2ehi3]
          · linarith only [h1682, h1683, hc25, hlam, hphi, u2ehi3]
        · linarith only [h1681, h1682, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h1414, h1681, hlam]
  · exact r1l7_10_12_25_L_I_L_R_H_I_s1 m hb0 hb2 hb5 h0 h1414

end R2N4
