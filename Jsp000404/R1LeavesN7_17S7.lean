import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10524000 in
set_option maxHeartbeats 10524000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3761 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4051 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h4052 | h4052
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4053 | h4053
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4054 | h4054
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4055 | h4055
        · linarith only [h0, h4, h4055, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4057 | h4057
          · linarith only [h0, h3761, h4057, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4059 | h4059
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4060 | h4060
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4061 | h4061
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4062 | h4062
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4063 | h4063
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4064 | h4064
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4065 | h4065
                        · rcases h0bigk with h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [hlam, p4066_0]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h4051, h4063, h4065, hc01, hc45, hlam, hphi, ht0b, ht5b, p4066_1]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h1, h4060, h4065, hc01, hc45, hlam, hphi, ht0b, ht5b, p4066_1]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h3761, h4051, h4063, h4065, hc01, hc45, hlam, hphi, ht0b, ht5b, p4066_1]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            rcases p4066_3 (m.d 0 1) (by simp) with h4071 | h4071
                            · rcases p4066_3 (m.d 0 2) (by simp) with h4072 | h4072
                              · linarith only [h0, h4072, hlam]
                              · linarith only [h4051, h4072, hlam]
                            · linarith only [h3, h4071, hlam]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h0, hlam, p4066_0]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [hlam, p4066_0]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h4, hlam, p4066_0]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h3761, hlam, p4066_1]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h3, h3761, h4062, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4066_1]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h1, hlam, p4066_1]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h4, hc02, hc23, hlam, hphi, p4066_1]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [hlam, p4066_0]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h0, h3761, h4, h4059, h4063, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p4066_1]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            rcases p4066_3 (m.d 0 1) (by simp) with h4085 | h4085
                            · rcases p4066_3 (m.d 0 2) (by simp) with h4086 | h4086
                              · linarith only [h4, h4086, hlam]
                              · linarith only [h4051, h4086, hlam]
                            · linarith only [h3, h4085, hlam]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h2, hlam, p4066_0]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h0, h4059, h4063, h4065, hc04, hc45, hlam, hphi, ht0b, ht5b, p4066_1]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h4052, hlam, p4066_0]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [hlam, p4066_0]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            rcases p4066_3 (m.d 0 1) (by simp) with h4094 | h4094
                            · rcases p4066_3 (m.d 0 2) (by simp) with h4095 | h4095
                              · linarith only [h3761, h4095, hlam]
                              · linarith only [h4051, h4095, hlam]
                            · linarith only [h3, h4094, hlam]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h3, hlam, p4066_0]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h4051, hlam, p4066_1]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h4053, hlam, p4066_0]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [h4054, hlam, p4066_1]
                          · have p4066_0 := h4066c.1
                            have p4066_1 := h4066c.2.1
                            have p4066_2 := h4066c.2.2.1
                            have p4066_3 := h4066c.2.2.2
                            linarith only [hlam, p4066_0]
                        · rcases h0bigk with h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c | h4104c
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [hlam, p4104_0]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h0, h4059, hc01, hc25, hlam, hphi, ht0b, ht5b, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h0, h4, h4059, h4064, h4065, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h0, h3761, h4059, h4064, h4065, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h4051, h4064, h4065, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h0, hlam, p4104_0]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [hlam, p4104_0]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h4, hlam, p4104_0]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h3761, hlam, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h3761, h4062, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h1, hlam, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h0, h4059, h4064, h4065, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [hlam, p4104_0]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h0, h3761, h4, h4059, h4064, h4065, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h4, h4051, h4064, h4065, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h2, hlam, p4104_0]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h0, h4059, h4064, h4065, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h4052, hlam, p4104_0]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [hlam, p4104_0]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h4051, h4064, h4065, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h3, hlam, p4104_0]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h4051, hlam, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h4053, hlam, p4104_0]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [h4054, hlam, p4104_1]
                          · have p4104_0 := h4104c.1
                            have p4104_1 := h4104c.2.1
                            have p4104_2 := h4104c.2.2.1
                            have p4104_3 := h4104c.2.2.2
                            linarith only [hlam, p4104_0]
                      · linarith only [h3761, h4054, h4064, hlam]
                    · linarith only [h4, h4053, h4063, hlam]
                  · linarith only [h4, h4052, h4062, hlam]
                · linarith only [h4057, h4059, h4061, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4134 | h4134
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4135 | h4135
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4136 | h4136
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4137 | h4137
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4138 | h4138
                        · rcases h0bigk with h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [hlam, p4139_0]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h4051, h4136, h4138, hc01, hc45, hlam, hphi, ht0b, ht5b, p4139_1]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h4052, h4055, h4060, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4139_1]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h3761, h4051, h4136, h4138, hc01, hc45, hlam, hphi, ht0b, ht5b, p4139_1]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            rcases p4139_3 (m.d 0 1) (by simp) with h4144 | h4144
                            · rcases p4139_3 (m.d 0 2) (by simp) with h4145 | h4145
                              · linarith only [h0, h4145, hlam]
                              · linarith only [h4051, h4145, hlam]
                            · linarith only [h3, h4144, hlam]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h0, hlam, p4139_0]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [hlam, p4139_0]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h4, hlam, p4139_0]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h3761, hlam, p4139_1]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4139_1]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h1, hlam, p4139_1]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h0, h4059, h4136, h4138, hc03, hc45, hlam, hphi, ht0b, ht5b, p4139_1]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [hlam, p4139_0]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h4, h4052, h4055, h4059, h4060, h4136, h4138, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4139_1]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            rcases p4139_3 (m.d 0 1) (by simp) with h4158 | h4158
                            · rcases p4139_3 (m.d 0 2) (by simp) with h4159 | h4159
                              · linarith only [h4, h4159, hlam]
                              · linarith only [h4051, h4159, hlam]
                            · linarith only [h3, h4158, hlam]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h2, hlam, p4139_0]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h0, h4059, h4136, h4138, hc04, hc45, hlam, hphi, ht0b, ht5b, p4139_1]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h4052, hlam, p4139_0]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [hlam, p4139_0]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            rcases p4139_3 (m.d 0 1) (by simp) with h4167 | h4167
                            · rcases p4139_3 (m.d 0 2) (by simp) with h4168 | h4168
                              · linarith only [h3761, h4168, hlam]
                              · linarith only [h4051, h4168, hlam]
                            · linarith only [h3, h4167, hlam]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h3, hlam, p4139_0]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h4051, hlam, p4139_1]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h4053, hlam, p4139_0]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [h4054, hlam, p4139_1]
                          · have p4139_0 := h4139c.1
                            have p4139_1 := h4139c.2.1
                            have p4139_2 := h4139c.2.2.1
                            have p4139_3 := h4139c.2.2.2
                            linarith only [hlam, p4139_0]
                        · linarith only [h4, h4052, h4054, h4055, h4059, h4060, h4136, h4138, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h3, h3761, h4059, h4134, h4136, h4137, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h4, h4052, h4055, h4060, h4136, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h4, h4052, h4135, hlam]
                · linarith only [h4055, h4059, h4060, h4134, hlam]
            · linarith only [h3761, h4051, h4059, hc12, hc24, hlam, hphi]
      · linarith only [h3761, h4051, h4054, hlam]
    · linarith only [h4, h4051, h4053, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4185 | h4185
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4186 | h4186
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4187 | h4187
        · linarith only [h0, h4, h4051, h4187, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4189 | h4189
          · linarith only [h0, h3761, h4189, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4191 | h4191
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4192 | h4192
              · linarith only [h0, h1, h4, h4052, h4191, h4192, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4194 | h4194
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4195 | h4195
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4196 | h4196
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4197 | h4197
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4198 | h4198
                        · rcases h0bigk with h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [hlam, p4199_0]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h0, h4191, h4196, h4198, hc01, hc45, hlam, hphi, ht0b, ht5b, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h0, h4, h4191, h4196, h4198, hc01, hc45, hlam, hphi, ht0b, ht5b, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h0, h4, h4052, h4191, h4196, h4198, hc01, hc45, hlam, hphi, ht0b, ht5b, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            rcases p4199_3 (m.d 0 1) (by simp) with h4204 | h4204
                            · rcases p4199_3 (m.d 0 2) (by simp) with h4205 | h4205
                              · linarith only [h0, h4205, hlam]
                              · linarith only [h4051, h4205, hlam]
                            · linarith only [h3, h4204, hlam]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h0, hlam, p4199_0]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [hlam, p4199_0]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h4, hlam, p4199_0]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h3761, hlam, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h4, h4052, h4195, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h1, hlam, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h4052, h4195, hc02, hc23, hlam, hphi, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [hlam, p4199_0]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h4052, hlam, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h4051, h4052, h4195, h4196, h4198, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h2, hlam, p4199_0]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h0, h4191, h4196, h4198, hc04, hc45, hlam, hphi, ht0b, ht5b, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h4052, h4195, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [hlam, p4199_0]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h4051, h4052, h4195, h4196, h4198, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h3, hlam, p4199_0]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h4051, hlam, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h4185, hlam, p4199_0]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [h4186, hlam, p4199_1]
                          · have p4199_0 := h4199c.1
                            have p4199_1 := h4199c.2.1
                            have p4199_2 := h4199c.2.2.1
                            have p4199_3 := h4199c.2.2.2
                            linarith only [hlam, p4199_0]
                        · linarith only [h1, h4052, h4186, h4187, h4191, h4196, h4198, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h3, h3761, h4191, h4194, h4196, h4197, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h4, h4052, h4195, h4196, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4232 | h4232
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4233 | h4233
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4234 | h4234
                        · rcases h0bigk with h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h0, h4191, h4232, h4234, hc01, hc45, hlam, hphi, ht0b, ht5b, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h0, h4, h4191, h4232, h4234, hc01, hc45, hlam, hphi, ht0b, ht5b, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h0, h3761, h4191, h4232, h4234, hc01, hc45, hlam, hphi, ht0b, ht5b, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            rcases p4235_3 (m.d 0 1) (by simp) with h4240 | h4240
                            · rcases p4235_3 (m.d 0 2) (by simp) with h4241 | h4241
                              · linarith only [h0, h4241, hlam]
                              · linarith only [h4051, h4241, hlam]
                            · linarith only [h3, h4240, hlam]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h0, hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4, hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h3761, hlam, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h3, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h1, hlam, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h0, h4052, h4191, hc04, hc25, hlam, hphi, ht0b, ht5b, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4052, hlam, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4, h4051, h4195, h4232, h4234, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h2, hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h0, h3761, h4191, h4232, h4234, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4052, hc03, hc34, hlam, hphi, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            rcases p4235_3 (m.d 0 1) (by simp) with h4259 | h4259
                            · rcases p4235_3 (m.d 0 2) (by simp) with h4260 | h4260
                              · linarith only [h3761, h4260, hlam]
                              · linarith only [h4051, h4260, hlam]
                            · linarith only [h3, h4259, hlam]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h3, hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4051, hlam, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4185, hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4186, hlam, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [hlam, p4235_0]
                        · linarith only [h4, h4195, h4234, hc02, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h0, h3, h3761, h4191, h4194, h4232, h4233, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h4, h4185, h4232, hlam]
                · linarith only [h4187, h4191, h4192, h4194, hlam]
            · linarith only [h4, h4051, h4191, hc12, hc23, hlam, hphi]
      · linarith only [h4, h4051, h4052, h4186, hlam]
    · linarith only [h4, h4051, h4185, hlam]

set_option maxHeartbeats 10524000 in
set_option maxHeartbeats 10524000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3761 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4051 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4276 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h4277 | h4277
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4278 | h4278
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4279 | h4279
      · linarith only [h0, h4, h4279, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4281 | h4281
        · linarith only [h0, h3761, h4281, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4283 | h4283
          · linarith only [h0, h4051, h4283, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4285 | h4285
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4286 | h4286
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4287 | h4287
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4288 | h4288
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4289 | h4289
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4290 | h4290
                      · rcases h0bigk with h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [hlam, p4291_0]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          rcases p4291_3 (m.d 0 1) (by simp) with h4293 | h4293
                          · rcases p4291_3 (m.d 0 2) (by simp) with h4294 | h4294
                            · linarith only [h0, h4294, hlam]
                            · rcases p4291_3 (m.d 0 3) (by simp) with h4296 | h4296
                              · linarith only [h1, h4296, hlam]
                              · linarith only [h4, h4296, hlam]
                          · linarith only [h0, h4293, hlam]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h2, h4276, h4285, h4290, hc01, hc45, hlam, hphi, ht0b, ht5b, p4291_1]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h2, h4285, h4290, hc01, hc45, hlam, hphi, ht0b, ht5b, p4291_1]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          rcases p4291_3 (m.d 0 1) (by simp) with h4302 | h4302
                          · rcases p4291_3 (m.d 0 2) (by simp) with h4303 | h4303
                            · linarith only [h0, h4303, hlam]
                            · rcases p4291_3 (m.d 0 3) (by simp) with h4305 | h4305
                              · linarith only [h1, h4305, hlam]
                              · linarith only [h4277, h4305, hlam]
                          · linarith only [h3, h4302, hlam]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h0, hlam, p4291_0]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [hlam, p4291_0]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h4, hlam, p4291_0]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h3761, hlam, p4291_1]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h4051, hlam, p4291_0]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h1, hlam, p4291_1]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h4, hc02, hc23, hlam, hphi, p4291_1]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [hlam, p4291_0]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h2, h4, h4285, h4290, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4291_1]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h3, h4, h4283, hc12, hc23, hlam, hphi, p4291_1]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h2, hlam, p4291_0]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p4291_1]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h4276, hlam, p4291_0]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [hlam, p4291_0]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h3, h4, h4276, h4283, hc12, hc23, hlam, hphi, p4291_1]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h3, hlam, p4291_0]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p4291_1]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h4277, hlam, p4291_0]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [h4278, hlam, p4291_1]
                        · have p4291_0 := h4291c.1
                          have p4291_1 := h4291c.2.1
                          have p4291_2 := h4291c.2.2.1
                          have p4291_3 := h4291c.2.2.2
                          linarith only [hlam, p4291_0]
                      · rcases h0bigk with h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [hlam, p4329_0]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          rcases p4329_3 (m.d 0 1) (by simp) with h4331 | h4331
                          · rcases p4329_3 (m.d 0 2) (by simp) with h4332 | h4332
                            · linarith only [h0, h4332, hlam]
                            · rcases p4329_3 (m.d 0 3) (by simp) with h4334 | h4334
                              · linarith only [h1, h4334, hlam]
                              · linarith only [h4, h4334, hlam]
                          · linarith only [h0, h4331, hlam]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h3, h4276, h4278, h4286, h4290, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h3, h4278, h4286, h4290, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h3, h4286, h4290, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h0, hlam, p4329_0]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [hlam, p4329_0]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h4, hlam, p4329_0]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h3761, hlam, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h4051, hlam, p4329_0]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h1, hlam, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [hlam, p4329_0]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h3, h4, h4278, h4286, h4290, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h3, h4, h4286, h4290, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h2, hlam, p4329_0]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h0, h3761, h4287, hc12, hc23, hlam, hphi, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h4276, hlam, p4329_0]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [hlam, p4329_0]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h3, h3761, h4286, h4287, h4290, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h3, hlam, p4329_0]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h0, h4051, h4287, h4289, hc12, hc23, hlam, hphi, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h4277, hlam, p4329_0]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [h4278, hlam, p4329_1]
                        · have p4329_0 := h4329c.1
                          have p4329_1 := h4329c.2.1
                          have p4329_2 := h4329c.2.2.1
                          have p4329_3 := h4329c.2.2.2
                          linarith only [hlam, p4329_0]
                    · linarith only [h3761, h4278, h4289, hlam]
                  · linarith only [h4, h4277, h4288, hlam]
                · linarith only [h4, h4276, h4287, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4364 | h4364
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4365 | h4365
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4366 | h4366
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4367 | h4367
                      · linarith only [h4285, h4286, h4367, hlam]
                      · rcases h0bigk with h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c | h4369c
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [hlam, p4369_0]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          rcases p4369_3 (m.d 0 1) (by simp) with h4371 | h4371
                          · rcases p4369_3 (m.d 0 2) (by simp) with h4372 | h4372
                            · linarith only [h0, h4372, hlam]
                            · rcases p4369_3 (m.d 0 3) (by simp) with h4374 | h4374
                              · linarith only [h1, h4374, hlam]
                              · linarith only [h4, h4374, hlam]
                          · linarith only [h0, h4371, hlam]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h4276, h4278, h4281, h4286, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h4278, h4281, h4286, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h4278, h4281, h4286, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h0, hlam, p4369_0]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [hlam, p4369_0]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h4, hlam, p4369_0]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h3761, hlam, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h4051, hlam, p4369_0]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h1, hlam, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [hlam, p4369_0]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h4, h4278, h4281, h4286, hc12, hc23, hlam, hphi, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h4, h4278, h4281, h4286, hc12, hc23, hlam, hphi, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h2, hlam, p4369_0]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h4276, hlam, p4369_0]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [hlam, p4369_0]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h4, h4276, h4278, h4281, h4286, hc12, hc23, hlam, hphi, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h3, hlam, p4369_0]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h0, h4051, h4366, hc12, hc24, hlam, hphi, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h4277, hlam, p4369_0]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [h4278, hlam, p4369_1]
                        · have p4369_0 := h4369c.1
                          have p4369_1 := h4369c.2.1
                          have p4369_2 := h4369c.2.2.1
                          have p4369_3 := h4369c.2.2.2
                          linarith only [hlam, p4369_0]
                    · linarith only [h3761, h4278, h4366, hlam]
                  · linarith only [h4, h4276, h4278, h4281, h4286, h4365, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h4, h4276, h4278, h4285, h4286, h4364, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4404 | h4404
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4405 | h4405
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4406 | h4406
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4407 | h4407
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4408 | h4408
                      · rcases h0bigk with h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [hlam, p4409_0]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          rcases p4409_3 (m.d 0 1) (by simp) with h4411 | h4411
                          · rcases p4409_3 (m.d 0 2) (by simp) with h4412 | h4412
                            · linarith only [h0, h4412, hlam]
                            · rcases p4409_3 (m.d 0 3) (by simp) with h4414 | h4414
                              · linarith only [h1, h4414, hlam]
                              · linarith only [h4, h4414, hlam]
                          · linarith only [h0, h4411, hlam]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h4276, h4285, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4409_1]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h2, h4404, hc01, hc45, hlam, hphi, ht0b, ht5b, p4409_1]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          rcases p4409_3 (m.d 0 1) (by simp) with h4420 | h4420
                          · rcases p4409_3 (m.d 0 2) (by simp) with h4421 | h4421
                            · linarith only [h0, h4421, hlam]
                            · rcases p4409_3 (m.d 0 3) (by simp) with h4423 | h4423
                              · linarith only [h1, h4423, hlam]
                              · linarith only [h4277, h4423, hlam]
                          · linarith only [h3, h4420, hlam]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h0, hlam, p4409_0]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [hlam, p4409_0]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h4, hlam, p4409_0]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h3761, hlam, p4409_1]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h4051, hlam, p4409_0]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h1, hlam, p4409_1]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p4409_1]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [hlam, p4409_0]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h4, h4276, h4279, h4285, hc12, hc23, hlam, hphi, p4409_1]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h0, h4, h4051, hc12, hc23, hlam, hphi, p4409_1]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h2, hlam, p4409_0]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p4409_1]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h4276, hlam, p4409_0]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [hlam, p4409_0]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h0, h4, h4051, h4276, hc12, hc23, hlam, hphi, p4409_1]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h3, hlam, p4409_0]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p4409_1]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h4277, hlam, p4409_0]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [h4278, hlam, p4409_1]
                        · have p4409_0 := h4409c.1
                          have p4409_1 := h4409c.2.1
                          have p4409_2 := h4409c.2.2.1
                          have p4409_3 := h4409c.2.2.2
                          linarith only [hlam, p4409_0]
                      · linarith only [h2, h4279, h4285, h4404, h4408, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h3761, h4, h4276, h4285, h4404, h4407, hc12, hc23, hlam, hphi]
                  · linarith only [h4, h4277, h4406, hlam]
                · linarith only [h4, h4276, h4405, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4451 | h4451
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4452 | h4452
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4453 | h4453
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4454 | h4454
                      · linarith only [h4, h4276, h4281, h4404, h4454, hc12, hc23, hlam, hphi]
                      · linarith only [h4, h4276, h4278, h4279, h4285, h4454, hc12, hc23, hlam, hphi]
                    · linarith only [h3761, h4278, h4453, hlam]
                  · linarith only [h4, h4277, h4452, hlam]
                · linarith only [h4, h4276, h4451, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4460 | h4460
      · linarith only [h0, h4, h4460, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4462 | h4462
        · linarith only [h0, h3761, h4462, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4464 | h4464
          · linarith only [h0, h4051, h4464, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4466 | h4466
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4467 | h4467
              · linarith only [h2, h4278, h4467, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4469 | h4469
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4470 | h4470
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4471 | h4471
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4472 | h4472
                      · linarith only [h0, h3761, h4, h4276, h4278, h4472, hc12, hc23, hlam, hphi]
                      · rcases h0bigk with h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c | h4474c
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          rcases p4474_3 (m.d 0 1) (by simp) with h4476 | h4476
                          · rcases p4474_3 (m.d 0 2) (by simp) with h4477 | h4477
                            · linarith only [h0, h4477, hlam]
                            · rcases p4474_3 (m.d 0 3) (by simp) with h4479 | h4479
                              · linarith only [h1, h4479, hlam]
                              · linarith only [h4, h4479, hlam]
                          · linarith only [h0, h4476, hlam]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h4277, hc01, hc35, hlam, hphi, ht0b, ht5b, p4474_1]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          rcases p4474_3 (m.d 0 1) (by simp) with h4484 | h4484
                          · rcases p4474_3 (m.d 0 2) (by simp) with h4485 | h4485
                            · linarith only [h0, h4485, hlam]
                            · rcases p4474_3 (m.d 0 3) (by simp) with h4487 | h4487
                              · linarith only [h1, h4487, hlam]
                              · linarith only [h4276, h4487, hlam]
                          · linarith only [h2, h4484, hlam]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          rcases p4474_3 (m.d 0 1) (by simp) with h4491 | h4491
                          · rcases p4474_3 (m.d 0 2) (by simp) with h4492 | h4492
                            · linarith only [h0, h4492, hlam]
                            · rcases p4474_3 (m.d 0 3) (by simp) with h4494 | h4494
                              · linarith only [h1, h4494, hlam]
                              · linarith only [h4277, h4494, hlam]
                          · linarith only [h3, h4491, hlam]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h0, hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h4, hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h3761, hlam, p4474_1]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h4051, hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h1, hlam, p4474_1]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p4474_1]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h0, h3761, h4, hc12, hc23, hlam, hphi, p4474_1]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h0, h3761, h4, h4278, hc12, hc23, hlam, hphi, p4474_1]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h2, hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h0, h4278, h4471, hc12, hc24, hlam, hphi, p4474_1]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h4276, hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h4278, hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h3, hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p4474_1]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h4277, hlam, p4474_0]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [h4278, h4471, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4474_1]
                        · have p4474_0 := h4474c.1
                          have p4474_1 := h4474c.2.1
                          have p4474_2 := h4474c.2.2.1
                          have p4474_3 := h4474c.2.2.2
                          linarith only [hlam, p4474_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4518 | h4518
                      · linarith only [h1, h4466, h4471, h4518, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c | h4520c
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          rcases p4520_3 (m.d 0 1) (by simp) with h4522 | h4522
                          · rcases p4520_3 (m.d 0 2) (by simp) with h4523 | h4523
                            · linarith only [h0, h4523, hlam]
                            · rcases p4520_3 (m.d 0 3) (by simp) with h4525 | h4525
                              · linarith only [h1, h4525, hlam]
                              · linarith only [h4, h4525, hlam]
                          · linarith only [h0, h4522, hlam]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h4276, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4520_1]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          rcases p4520_3 (m.d 0 1) (by simp) with h4530 | h4530
                          · rcases p4520_3 (m.d 0 2) (by simp) with h4531 | h4531
                            · linarith only [h0, h4531, hlam]
                            · rcases p4520_3 (m.d 0 3) (by simp) with h4533 | h4533
                              · linarith only [h1, h4533, hlam]
                              · linarith only [h4276, h4533, hlam]
                          · linarith only [h2, h4530, hlam]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          rcases p4520_3 (m.d 0 1) (by simp) with h4537 | h4537
                          · rcases p4520_3 (m.d 0 2) (by simp) with h4538 | h4538
                            · linarith only [h0, h4538, hlam]
                            · rcases p4520_3 (m.d 0 3) (by simp) with h4540 | h4540
                              · linarith only [h1, h4540, hlam]
                              · linarith only [h4277, h4540, hlam]
                          · linarith only [h3, h4537, hlam]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h0, hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h4, hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h3761, hlam, p4520_1]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h4051, hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h1, hlam, p4520_1]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p4520_1]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h0, h3761, h4, hc12, hc23, hlam, hphi, p4520_1]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h0, h4, h4051, hc12, hc23, hlam, hphi, p4520_1]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h2, hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p4520_1]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h4276, hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h4278, hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h3, hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p4520_1]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h4277, hlam, p4520_0]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [h4278, hc04, hc45, hlam, hphi, p4520_1]
                        · have p4520_0 := h4520c.1
                          have p4520_1 := h4520c.2.1
                          have p4520_2 := h4520c.2.2.1
                          have p4520_3 := h4520c.2.2.2
                          linarith only [hlam, p4520_0]
                  · linarith only [h4, h4277, h4470, hlam]
                · linarith only [h4, h4276, h4469, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4566 | h4566
              · linarith only [h2, h4276, h4278, h4466, h4566, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4568 | h4568
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4569 | h4569
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4570 | h4570
                    · linarith only [h4276, h4278, h4460, h4466, h4570, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4572 | h4572
                      · linarith only [h3761, h4276, h4570, h4572, hlam]
                      · rcases h0bigk with h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c | h4574c
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          rcases p4574_3 (m.d 0 1) (by simp) with h4576 | h4576
                          · rcases p4574_3 (m.d 0 2) (by simp) with h4577 | h4577
                            · linarith only [h0, h4577, hlam]
                            · rcases p4574_3 (m.d 0 3) (by simp) with h4579 | h4579
                              · linarith only [h1, h4579, hlam]
                              · linarith only [h4, h4579, hlam]
                          · linarith only [h0, h4576, hlam]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h4277, hc01, hc35, hlam, hphi, ht0b, ht5b, p4574_1]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h4276, h4460, h4466, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4574_1]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h4276, h4278, h4460, h4466, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4574_1]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h0, hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h4, hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h3761, hlam, p4574_1]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h4051, hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h1, hlam, p4574_1]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p4574_1]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h4, h4276, h4460, h4466, hc12, hc23, hlam, hphi, p4574_1]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h0, h4, h4051, hc12, hc23, hlam, hphi, p4574_1]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h2, hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p4574_1]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h4276, hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h4278, hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h3, hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p4574_1]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h4277, hlam, p4574_0]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [h4278, hc04, hc45, hlam, hphi, p4574_1]
                        · have p4574_0 := h4574c.1
                          have p4574_1 := h4574c.2.1
                          have p4574_2 := h4574c.2.2.1
                          have p4574_3 := h4574c.2.2.2
                          linarith only [hlam, p4574_0]
                  · linarith only [h4, h4276, h4460, h4466, h4569, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h4, h4276, h4568, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4608 | h4608
    · linarith only [h4276, h4277, h4608, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4610 | h4610
      · linarith only [h0, h4, h4610, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4612 | h4612
        · linarith only [h0, h3761, h4612, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4614 | h4614
          · linarith only [h0, h4051, h4614, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4616 | h4616
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4617 | h4617
              · linarith only [h2, h4608, h4617, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4619 | h4619
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4620 | h4620
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4621 | h4621
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4622 | h4622
                      · linarith only [h1, h4277, h4608, h4616, h4620, h4622, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases h0bigk with h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          rcases p4624_3 (m.d 0 1) (by simp) with h4626 | h4626
                          · rcases p4624_3 (m.d 0 2) (by simp) with h4627 | h4627
                            · linarith only [h0, h4627, hlam]
                            · rcases p4624_3 (m.d 0 3) (by simp) with h4629 | h4629
                              · linarith only [h1, h4629, hlam]
                              · linarith only [h4, h4629, hlam]
                          · linarith only [h0, h4626, hlam]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h1, h4616, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          rcases p4624_3 (m.d 0 1) (by simp) with h4634 | h4634
                          · rcases p4624_3 (m.d 0 2) (by simp) with h4635 | h4635
                            · linarith only [h0, h4635, hlam]
                            · rcases p4624_3 (m.d 0 3) (by simp) with h4637 | h4637
                              · linarith only [h1, h4637, hlam]
                              · linarith only [h4276, h4637, hlam]
                          · linarith only [h2, h4634, hlam]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h1, h4277, h4616, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h0, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h3761, hlam, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4051, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h1, hlam, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h0, h4277, h4619, h4621, h4622, hc12, hc23, hlam, hphi, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h0, h3761, h4277, h4619, h4621, h4622, hc12, hc23, hlam, hphi, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4277, hlam, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h2, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h0, h3761, h4619, hc12, hc23, hlam, hphi, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4276, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4608, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h3, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h1, h4277, h4616, h4619, h4621, h4622, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4277, h4619, h4621, h4622, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [hlam, p4624_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4662 | h4662
                      · linarith only [h1, h4616, h4621, h4662, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c | h4664c
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [hlam, p4664_0]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          rcases p4664_3 (m.d 0 1) (by simp) with h4666 | h4666
                          · rcases p4664_3 (m.d 0 2) (by simp) with h4667 | h4667
                            · linarith only [h0, h4667, hlam]
                            · rcases p4664_3 (m.d 0 3) (by simp) with h4669 | h4669
                              · linarith only [h1, h4669, hlam]
                              · linarith only [h4, h4669, hlam]
                          · linarith only [h0, h4666, hlam]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h1, h4616, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4664_1]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          rcases p4664_3 (m.d 0 1) (by simp) with h4674 | h4674
                          · rcases p4664_3 (m.d 0 2) (by simp) with h4675 | h4675
                            · linarith only [h0, h4675, hlam]
                            · rcases p4664_3 (m.d 0 3) (by simp) with h4677 | h4677
                              · linarith only [h1, h4677, hlam]
                              · linarith only [h4276, h4677, hlam]
                          · linarith only [h2, h4674, hlam]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h1, h4277, h4616, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4664_1]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h0, hlam, p4664_0]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [hlam, p4664_0]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h4, hlam, p4664_0]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h3761, hlam, p4664_1]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h4051, hlam, p4664_0]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h1, hlam, p4664_1]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h0, h4277, hc12, hc35, hlam, hphi, ht23, p4664_1]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [hlam, p4664_0]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h4277, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4664_1]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h4277, hlam, p4664_1]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h2, hlam, p4664_0]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p4664_1]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h4276, hlam, p4664_0]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [hlam, p4664_0]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h4608, hlam, p4664_0]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h3, hlam, p4664_0]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p4664_1]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h4277, hc03, hc35, hlam, hphi, p4664_1]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [h4608, hc04, hc45, hlam, hphi, p4664_1]
                        · have p4664_0 := h4664c.1
                          have p4664_1 := h4664c.2.1
                          have p4664_2 := h4664c.2.2.1
                          have p4664_3 := h4664c.2.2.2
                          linarith only [hlam, p4664_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4702 | h4702
                    · linarith only [h2, h4608, h4612, h4619, h4620, h4702, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4704 | h4704
                      · linarith only [h1, h4616, h4702, h4704, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c | h4706c
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [hlam, p4706_0]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          rcases p4706_3 (m.d 0 1) (by simp) with h4708 | h4708
                          · rcases p4706_3 (m.d 0 2) (by simp) with h4709 | h4709
                            · linarith only [h0, h4709, hlam]
                            · rcases p4706_3 (m.d 0 3) (by simp) with h4711 | h4711
                              · linarith only [h1, h4711, hlam]
                              · linarith only [h4, h4711, hlam]
                          · linarith only [h0, h4708, hlam]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h4276, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4706_1]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          rcases p4706_3 (m.d 0 1) (by simp) with h4716 | h4716
                          · rcases p4706_3 (m.d 0 2) (by simp) with h4717 | h4717
                            · linarith only [h0, h4717, hlam]
                            · rcases p4706_3 (m.d 0 3) (by simp) with h4719 | h4719
                              · linarith only [h1, h4719, hlam]
                              · linarith only [h4276, h4719, hlam]
                          · linarith only [h2, h4716, hlam]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h1, h4277, h4616, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4706_1]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h0, hlam, p4706_0]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [hlam, p4706_0]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h4, hlam, p4706_0]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h3761, hlam, p4706_1]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h4051, hlam, p4706_0]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h1, hlam, p4706_1]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h0, h4, h4620, h4704, hc12, hc45, hlam, hphi, ht23, ht34, p4706_1]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [hlam, p4706_0]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h2, h4, h4612, h4620, h4704, hc12, hc45, hlam, hphi, ht23, ht34, p4706_1]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h4277, hlam, p4706_1]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h2, hlam, p4706_0]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p4706_1]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h4276, hlam, p4706_0]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [hlam, p4706_0]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h4608, hlam, p4706_0]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h3, hlam, p4706_0]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h0, h4051, h4620, h4704, hc12, hc45, hlam, hphi, ht23, ht34, p4706_1]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h4051, h4620, h4704, hc03, hc45, hlam, hphi, ht34, p4706_1]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [h4051, h4620, h4704, hc04, hc45, hlam, hphi, p4706_1]
                        · have p4706_0 := h4706c.1
                          have p4706_1 := h4706c.2.1
                          have p4706_2 := h4706c.2.2.1
                          have p4706_3 := h4706c.2.2.2
                          linarith only [hlam, p4706_0]
                · linarith only [h0, h1, h4, h4616, h4619, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h4276, h4277, h4616, hc13, hc35, hlam, hphi]

end R2N4
