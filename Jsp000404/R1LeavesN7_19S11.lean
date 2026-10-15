import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5434000 in
set_option maxHeartbeats 5434000 in
theorem r1l7_21_14_H_I_L_I_s6_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6110 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h6504 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h7104 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7105 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0 := hg0
  have h5235 := hg5235
  rcases m.htr 0 4 5 (by decide) (by decide) with h7106 | h7106
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7107 | h7107
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7108 | h7108
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7109 | h7109
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7110 | h7110
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7111 | h7111
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7112 | h7112
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7113 | h7113
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7114 | h7114
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7115 | h7115
                    · rcases h1bigk with h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c | h7116c
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h0, hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h5235, hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h6110, hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h6504, hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7116_1]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7116_1]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p7116_1]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7116_1]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7116_1]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h7107, hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h6504, h7107, h7112, hc01, hc12, hlam, hphi, p7116_1]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h6504, h7107, hc01, hc12, hlam, hphi, p7116_1]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7116_1]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h7108, hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h7110, hlam, p7116_1]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h6504, h7107, h7110, hc01, hc12, hlam, hphi, p7116_1]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7116_1]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h7109, hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h7111, hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [h7112, hlam, p7116_0]
                      · have p7116_0 := h7116c.1
                        have p7116_1 := h7116c.2.1
                        have p7116_2 := h7116c.2.2.1
                        have p7116_3 := h7116c.2.2.2
                        linarith only [hlam, p7116_0]
                    · rcases h1bigk with h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c | h7142c
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h0, hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h5235, hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h6110, hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h6504, hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7142_1]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7142_1]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p7142_1]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7142_1]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7142_1]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h7107, hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h6110, h7107, hc01, hc12, hlam, hphi, p7142_1]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h6504, h7107, hc01, hc12, hlam, hphi, p7142_1]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7142_1]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h7108, hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h7110, hlam, p7142_1]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h6504, h7107, h7110, hc01, hc12, hlam, hphi, p7142_1]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7142_1]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h7109, hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h7111, hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [h7112, hlam, p7142_0]
                      · have p7142_0 := h7142c.1
                        have p7142_1 := h7142c.2.1
                        have p7142_2 := h7142c.2.2.1
                        have p7142_3 := h7142c.2.2.2
                        linarith only [hlam, p7142_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7168 | h7168
                    · linarith only [h7107, h7113, h7114, h7168, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases h1bigk with h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h0, hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h5235, hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h6110, hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h6504, hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7170_1]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7170_1]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h6110, h7106, h7113, h7114, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7170_1]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7170_1]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7170_1]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h7107, hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h6110, h7106, h7107, h7113, h7114, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7170_1]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h6504, h7107, hc01, hc12, hlam, hphi, p7170_1]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7170_1]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h7108, hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h7110, hlam, p7170_1]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h6504, h7107, h7110, hc01, hc12, hlam, hphi, p7170_1]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7170_1]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h7109, hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h7111, hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [h7112, hlam, p7170_0]
                      · have p7170_0 := h7170c.1
                        have p7170_1 := h7170c.2.1
                        have p7170_2 := h7170c.2.2.1
                        have p7170_3 := h7170c.2.2.2
                        linarith only [hlam, p7170_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7196 | h7196
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7197 | h7197
                    · rcases h1bigk with h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c | h7198c
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h0, hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h5235, hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h6110, hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h6504, hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7198_1]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7198_1]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p7198_1]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7198_1]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7198_1]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h7107, hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h6504, h7107, h7112, hc01, hc12, hlam, hphi, p7198_1]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h6504, h7107, hc01, hc12, hlam, hphi, p7198_1]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7198_1]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h7108, hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h7110, hlam, p7198_1]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h6504, h7107, h7110, hc01, hc12, hlam, hphi, p7198_1]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7198_1]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h7109, hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h7111, hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [h7112, hlam, p7198_0]
                      · have p7198_0 := h7198c.1
                        have p7198_1 := h7198c.2.1
                        have p7198_2 := h7198c.2.2.1
                        have p7198_3 := h7198c.2.2.2
                        linarith only [hlam, p7198_0]
                    · linarith only [h7113, h7196, h7197, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7225 | h7225
                    · rcases h1bigk with h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c | h7226c
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h0, hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h5235, hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h6110, hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h6504, hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7226_1]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7226_1]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p7226_1]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7226_1]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7226_1]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h7107, hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h6110, h7105, h7107, h7113, h7196, h7225, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7226_1]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h6504, h7107, hc01, hc12, hlam, hphi, p7226_1]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7226_1]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h7108, hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h7110, hlam, p7226_1]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h6504, h7107, h7110, hc01, hc12, hlam, hphi, p7226_1]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7226_1]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h7109, hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h7111, hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [h7112, hlam, p7226_0]
                      · have p7226_0 := h7226c.1
                        have p7226_1 := h7226c.2.1
                        have p7226_2 := h7226c.2.2.1
                        have p7226_3 := h7226c.2.2.2
                        linarith only [hlam, p7226_0]
                    · rcases h1bigk with h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c | h7252c
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h0, hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h5235, hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h6110, hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h6504, hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7252_1]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h6110, h7106, h7110, h7225, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7252_1]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h6110, h7106, h7225, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7252_1]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7252_1]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7252_1]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h7107, hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h6110, h7106, h7107, h7225, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7252_1]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h6504, h7107, hc01, hc12, hlam, hphi, p7252_1]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7252_1]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h7108, hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h7110, hlam, p7252_1]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h6504, h7107, h7110, hc01, hc12, hlam, hphi, p7252_1]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7252_1]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h7109, hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h7111, hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [h7112, hlam, p7252_0]
                      · have p7252_0 := h7252c.1
                        have p7252_1 := h7252c.2.1
                        have p7252_2 := h7252c.2.2.1
                        have p7252_3 := h7252c.2.2.2
                        linarith only [hlam, p7252_0]
              · linarith only [h5235, h6110, h7105, h7106, h7107, h7112, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7279 | h7279
              · linarith only [h7110, h7111, h7279, hlam]
              · linarith only [h5235, h6110, h7105, h7106, h7111, h7279, hc01, hc35, hlam, hphi, ht12, ht23]
          · linarith only [h5235, h7105, h7110, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7283 | h7283
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7284 | h7284
            · linarith only [h7107, h7109, h7284, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7286 | h7286
              · linarith only [h7108, h7109, h7286, hlam]
              · linarith only [h5235, h6110, h7105, h7106, h7107, h7286, hc01, hc12, hlam, hphi]
          · linarith only [h5235, h7105, h7283, hlam]
      · linarith only [h0, h7104, h7108, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7291 | h7291
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7292 | h7292
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7293 | h7293
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7294 | h7294
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7295 | h7295
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7296 | h7296
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7297 | h7297
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7298 | h7298
                    · rcases h1bigk with h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c | h7299c
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h0, hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h5235, hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h6110, hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h6504, hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h7107, hc01, hc23, hlam, hphi, ht12, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h7107, hlam, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h6504, h7107, h7295, hc01, hc23, hlam, hphi, ht12, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h6504, h7107, hc01, hc23, hlam, hphi, ht12, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h0, h7107, hc02, hc23, hlam, hphi, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h6504, h7107, h7295, hc01, hc23, hlam, hphi, ht12, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h6504, h7107, hc01, hc23, hlam, hphi, ht12, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h7291, hc01, hc12, hlam, hphi, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h7291, hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h7293, hlam, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h6504, h7107, h7291, hc01, hc23, hlam, hphi, ht12, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7299_1]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h7292, hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h7294, hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [h7295, hlam, p7299_0]
                      · have p7299_0 := h7299c.1
                        have p7299_1 := h7299c.2.1
                        have p7299_2 := h7299c.2.2.1
                        have p7299_3 := h7299c.2.2.2
                        linarith only [hlam, p7299_0]
                    · linarith only [h0, h7104, h7107, h7297, h7298, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7326 | h7326
                    · linarith only [h7296, h7297, h7326, hlam]
                    · rcases h1bigk with h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h0, hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h5235, hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h6110, hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h6504, hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h7107, hc01, hc23, hlam, hphi, ht12, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h7107, hlam, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h7107, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h7107, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h7107, hc01, hc23, hlam, hphi, ht12, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h0, h7107, hc02, hc23, hlam, hphi, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h6110, h7106, h7107, h7296, h7297, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h6504, h7107, hc01, hc23, hlam, hphi, ht12, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h7291, hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h7293, hlam, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h6504, h7291, hc01, hc12, hlam, hphi, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7328_1]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h7292, hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h7294, hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [h7295, hlam, p7328_0]
                      · have p7328_0 := h7328c.1
                        have p7328_1 := h7328c.2.1
                        have p7328_2 := h7328c.2.2.1
                        have p7328_3 := h7328c.2.2.2
                        linarith only [hlam, p7328_0]
                · linarith only [h0, h7107, h7296, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h6110, h7104, h7106, h7295, hc01, hc12, hlam, hphi]
            · linarith only [h7107, h7292, h7294, hlam]
          · linarith only [h5235, h7105, h7293, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7358 | h7358
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7359 | h7359
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7360 | h7360
              · linarith only [h7291, h7292, h7360, hlam]
              · linarith only [h0, h6110, h7104, h7106, h7360, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7363 | h7363
              · linarith only [h7291, h7292, h7363, hlam]
              · linarith only [h0, h6110, h7104, h7106, h7107, h7359, h7363, hc01, hc35, hlam, hphi, ht12, ht23]
          · linarith only [h5235, h7105, h7358, hlam]
      · linarith only [h0, h7104, h7291, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7368 | h7368
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7369 | h7369
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7370 | h7370
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7371 | h7371
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7372 | h7372
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7373 | h7373
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7374 | h7374
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7375 | h7375
                  · linarith only [h0, h6110, h7104, h7106, h7375, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7377 | h7377
                    · linarith only [h5235, h6110, h7105, h7106, h7377, hc01, hc13, hlam, hphi]
                    · rcases h1bigk with h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h0, hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h5235, hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h6110, hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h6504, hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7379_1]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7379_1]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h6110, h7106, h7373, hc01, hc12, hlam, hphi, p7379_1]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7379_1]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7379_1]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h7368, hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h6110, h7106, h7368, h7373, hc01, hc12, hlam, hphi, p7379_1]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h6504, h7368, hc01, hc12, hlam, hphi, p7379_1]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7379_1]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h7369, hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h7371, hlam, p7379_1]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h6504, h7368, h7371, hc01, hc12, hlam, hphi, p7379_1]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7379_1]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h7370, hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h7372, hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [h7373, hlam, p7379_0]
                      · have p7379_0 := h7379c.1
                        have p7379_1 := h7379c.2.1
                        have p7379_2 := h7379c.2.2.1
                        have p7379_3 := h7379c.2.2.2
                        linarith only [hlam, p7379_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7405 | h7405
                  · linarith only [h7105, h7106, h7374, h7405, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7407 | h7407
                    · linarith only [h7105, h7106, h7407, hlam]
                    · rcases h1bigk with h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h0, hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h5235, hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h6110, hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h6504, hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7409_1]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7409_1]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h6504, h7373, hc01, hc12, hlam, hphi, p7409_1]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7409_1]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7409_1]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h7368, hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h6504, h7368, h7373, hc01, hc12, hlam, hphi, p7409_1]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h6504, h7368, hc01, hc12, hlam, hphi, p7409_1]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7409_1]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h7369, hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h7371, hlam, p7409_1]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h6504, h7368, h7371, hc01, hc12, hlam, hphi, p7409_1]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7409_1]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h7370, hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h7372, hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [h7373, hlam, p7409_0]
                      · have p7409_0 := h7409c.1
                        have p7409_1 := h7409c.2.1
                        have p7409_2 := h7409c.2.2.1
                        have p7409_3 := h7409c.2.2.2
                        linarith only [hlam, p7409_0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7435 | h7435
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7436 | h7436
                  · linarith only [h6110, h7373, h7436, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7438 | h7438
                    · linarith only [h6110, h7105, h7373, h7438, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c | h7440c
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h0, hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h5235, hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h6110, hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h6504, hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h7372, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h7368, hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h6110, h7368, hc01, hc12, hlam, hphi, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h6110, h6504, h7106, h7368, hc01, hc12, hlam, hphi, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h7369, hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h7371, hlam, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h7373, hlam, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h7370, hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h7372, hlam, p7440_0]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [h7373, hc14, hc45, hlam, hphi, p7440_1]
                      · have p7440_0 := h7440c.1
                        have p7440_1 := h7440c.2.1
                        have p7440_2 := h7440c.2.2.1
                        have p7440_3 := h7440c.2.2.2
                        linarith only [hlam, p7440_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7466 | h7466
                  · linarith only [h6504, h7105, h7106, h7373, h7435, h7466, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7468 | h7468
                    · linarith only [h6110, h7105, h7373, h7468, hlam]
                    · rcases h1bigk with h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h0, hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h5235, hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h6110, hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h6504, hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h6110, h7105, h7435, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h7368, hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h6110, h7368, hc01, hc12, hlam, hphi, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h6504, h7368, hc01, hc12, hlam, hphi, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h7369, hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h7371, hlam, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h7373, hlam, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h7370, hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h7372, hlam, p7470_0]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [h7373, hc14, hc45, hlam, hphi, p7470_1]
                      · have p7470_0 := h7470c.1
                        have p7470_1 := h7470c.2.1
                        have p7470_2 := h7470c.2.2.1
                        have p7470_3 := h7470c.2.2.2
                        linarith only [hlam, p7470_0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7496 | h7496
              · linarith only [h6110, h7106, h7371, h7372, h7496, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7498 | h7498
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7499 | h7499
                  · linarith only [h6110, h7496, h7499, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7501 | h7501
                    · linarith only [h6110, h7368, h7496, h7498, h7501, hc01, hc12, hlam, hphi]
                    · rcases h1bigk with h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c | h7503c
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [hlam, p7503_0]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h0, hlam, p7503_0]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h5235, hlam, p7503_0]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h6110, hlam, p7503_0]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h6504, hlam, p7503_0]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [hlam, p7503_0]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h5235, h7372, hc01, hc12, hlam, hphi, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h7368, hlam, p7503_0]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [hlam, p7503_0]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h6110, h7370, h7372, hc01, hc12, hlam, hphi, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h7372, hlam, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h7369, hlam, p7503_0]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h7371, hlam, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [hlam, p7503_0]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h7496, hlam, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h7370, hc01, hc12, hlam, hphi, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h7370, hlam, p7503_0]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h5235, h7370, hc01, hc12, hlam, hphi, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [h6110, h7372, h7501, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p7503_1]
                      · have p7503_0 := h7503c.1
                        have p7503_1 := h7503c.2.1
                        have p7503_2 := h7503c.2.2.1
                        have p7503_3 := h7503c.2.2.2
                        linarith only [hlam, p7503_0]
                · linarith only [h5235, h7105, h7372, h7498, hc23, hc35, hlam, hphi]
          · linarith only [h5235, h7105, h7371, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7531 | h7531
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7532 | h7532
            · linarith only [h7368, h7370, h7532, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7534 | h7534
              · linarith only [h6110, h7106, h7369, h7370, h7534, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7536 | h7536
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7537 | h7537
                  · linarith only [h6110, h7534, h7537, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h7368, h7370, h7536, h7537, hc34, hc45, hlam, hphi]
                · linarith only [h5235, h7105, h7532, h7536, hc23, hc35, hlam, hphi]
          · linarith only [h5235, h7105, h7531, hlam]
      · linarith only [h0, h7104, h7369, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7543 | h7543
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7544 | h7544
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7545 | h7545
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7546 | h7546
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7547 | h7547
              · linarith only [h6110, h7106, h7368, h7543, h7547, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7549 | h7549
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7550 | h7550
                  · linarith only [h6110, h7547, h7550, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7552 | h7552
                    · linarith only [h0, h6110, h7104, h7368, h7547, h7549, h7552, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases h1bigk with h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [hlam, p7554_0]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h0, hlam, p7554_0]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h5235, hlam, p7554_0]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h6110, hlam, p7554_0]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h6504, hlam, p7554_0]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h7368, hc01, hc23, hlam, hphi, ht12, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [hlam, p7554_0]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h7368, hlam, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h6110, h7368, hc01, hc23, hlam, hphi, ht12, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h6504, h7368, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h0, h7368, hc02, hc23, hlam, hphi, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [hlam, p7554_0]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h6110, h7368, hc01, hc23, hlam, hphi, ht12, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h6504, h7368, hc01, hc23, hlam, hphi, ht12, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h7543, hc01, hc12, hlam, hphi, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h7543, hlam, p7554_0]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h7545, hlam, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [hlam, p7554_0]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h7547, hlam, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h7544, hlam, p7554_0]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h7546, hlam, p7554_0]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [h7368, h7544, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7554_1]
                      · have p7554_0 := h7554c.1
                        have p7554_1 := h7554c.2.1
                        have p7554_2 := h7554c.2.2.1
                        have p7554_3 := h7554c.2.2.2
                        linarith only [hlam, p7554_0]
                · linarith only [h0, h7368, h7549, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h7368, h7544, h7546, hlam]
          · linarith only [h6504, h7105, h7106, h7368, h7544, h7545, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7583 | h7583
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7584 | h7584
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7585 | h7585
              · linarith only [h6110, h7106, h7543, h7544, h7585, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7587 | h7587
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7588 | h7588
                  · linarith only [h6110, h7104, h7585, h7588, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7590 | h7590
                    · linarith only [h0, h7104, h7544, h7587, h7588, h7590, hlam]
                    · rcases h1bigk with h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c | h7592c
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [hlam, p7592_0]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h0, hlam, p7592_0]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h5235, hlam, p7592_0]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h6110, hlam, p7592_0]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h6504, hlam, p7592_0]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h7544, h7588, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [hlam, p7592_0]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h7368, hlam, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h6110, h7544, h7588, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h7544, hlam, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h7368, hc01, hc23, hlam, hphi, ht12, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h0, h7368, hc02, hc23, hlam, hphi, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [hlam, p7592_0]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h6110, h7368, hc01, hc23, hlam, hphi, ht12, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h6504, h7368, hc01, hc23, hlam, hphi, ht12, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h7543, hc01, hc12, hlam, hphi, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h7543, hlam, p7592_0]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h7583, hlam, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [hlam, p7592_0]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h7585, hlam, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h7544, h7588, hc12, hc45, hlam, hphi, ht23, ht34, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h7584, hlam, p7592_0]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [h6110, h7544, h7588, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p7592_1]
                      · have p7592_0 := h7592c.1
                        have p7592_1 := h7592c.2.1
                        have p7592_2 := h7592c.2.2.1
                        have p7592_3 := h7592c.2.2.2
                        linarith only [hlam, p7592_0]
                · linarith only [h5235, h7105, h7368, h7587, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7619 | h7619
              · linarith only [h6110, h7106, h7368, h7543, h7619, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7621 | h7621
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7622 | h7622
                  · linarith only [h6110, h7619, h7622, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7624 | h7624
                    · linarith only [h0, h7104, h7544, h7621, h7622, h7624, hlam]
                    · rcases h1bigk with h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c | h7626c
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [hlam, p7626_0]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h0, hlam, p7626_0]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h5235, hlam, p7626_0]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h6110, hlam, p7626_0]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h6504, hlam, p7626_0]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h7368, h7584, h7624, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [hlam, p7626_0]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h7368, hlam, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h6110, h7368, h7584, h7624, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h7544, hlam, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h7584, h7624, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h0, h7584, h7624, hc02, hc45, hlam, hphi, ht23, ht34, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [hlam, p7626_0]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h6110, h7584, h7624, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h7584, hlam, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h7543, hlam, p7626_0]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h7583, hlam, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [hlam, p7626_0]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h7619, hlam, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h7544, h7622, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h0, h7544, h7622, hc02, hc45, hlam, hphi, ht23, ht34, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h5235, h7544, h7622, hc03, hc45, hlam, hphi, ht34, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [h6110, h7544, h7622, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p7626_1]
                      · have p7626_0 := h7626c.1
                        have p7626_1 := h7626c.2.1
                        have p7626_2 := h7626c.2.2.1
                        have p7626_3 := h7626c.2.2.2
                        linarith only [hlam, p7626_0]
                · linarith only [h6110, h7105, h7368, h7543, h7621, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
          · linarith only [h0, h5235, h7104, h7105, h7368, h7583, hc01, hc23, hlam, hphi, ht12]
      · linarith only [h0, h7104, h7543, hlam]

end R2N4
