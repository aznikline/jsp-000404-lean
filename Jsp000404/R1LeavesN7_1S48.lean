import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19434000 in
set_option maxHeartbeats 19434000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h22350 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h30132 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h30701 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h31058 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  rcases m.htr 0 3 5 (by decide) (by decide) with h31059 | h31059
  · rcases m.htr 0 4 5 (by decide) (by decide) with h31060 | h31060
    · rcases m.htr 1 2 3 (by decide) (by decide) with h31061 | h31061
      · rcases m.htr 1 2 4 (by decide) (by decide) with h31062 | h31062
        · rcases m.htr 1 2 5 (by decide) (by decide) with h31063 | h31063
          · rcases m.htr 1 3 4 (by decide) (by decide) with h31064 | h31064
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31065 | h31065
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31066 | h31066
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31067 | h31067
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31068 | h31068
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31069 | h31069
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31070 | h31070
                        · rcases h0bigk with h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c | h31071c
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [hlam, p31071_0]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h0, hlam, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h15532, hlam, p31071_0]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h18443, hlam, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h20697, hlam, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h30701, h31061, h31067, h31069, hc01, hc12, hlam, hphi, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [hlam, p31071_0]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h22350, hlam, p31071_0]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h30132, hlam, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h30701, hlam, p31071_0]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h22350, h31061, hc01, hc12, hlam, hphi, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h0, h22350, h31061, hc01, hc12, hlam, hphi, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [hlam, p31071_0]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h18443, h22350, h31061, hc01, hc12, hlam, hphi, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h0, h22350, h30701, h31061, hc01, hc12, hlam, hphi, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h30132, h31061, h31067, hc01, hc12, hlam, hphi, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h0, h30132, h31061, h31067, hc01, hc12, hlam, hphi, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h31058, hlam, p31071_0]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [hlam, p31071_0]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h0, h30132, h30701, h31061, h31067, hc01, hc12, hlam, hphi, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h30701, h31061, h31067, h31069, hc01, hc12, hlam, hphi, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h0, h30701, h31061, h31067, h31069, hc01, hc12, hlam, hphi, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h31059, hlam, p31071_0]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [h31060, hlam, p31071_1]
                          · have p31071_0 := h31071c.1
                            have p31071_1 := h31071c.2.1
                            have p31071_2 := h31071c.2.2.1
                            have p31071_3 := h31071c.2.2.2
                            linarith only [hlam, p31071_0]
                        · rcases h0bigk with h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c | h31097c
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [hlam, p31097_0]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h0, hlam, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h15532, hlam, p31097_0]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h18443, hlam, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h20697, hlam, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h22350, h31061, hc01, hc12, hlam, hphi, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [hlam, p31097_0]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h22350, hlam, p31097_0]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h30132, hlam, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h30701, hlam, p31097_0]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h22350, h31061, hc01, hc12, hlam, hphi, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h0, h22350, h31061, hc01, hc12, hlam, hphi, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [hlam, p31097_0]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h22350, h31060, h31061, h31070, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h20697, h22350, h31061, hc01, hc12, hlam, hphi, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h30132, h31061, h31067, hc01, hc12, hlam, hphi, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h0, h30132, h31061, h31067, hc01, hc12, hlam, hphi, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h31058, hlam, p31097_0]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [hlam, p31097_0]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h0, h30132, h30701, h31061, h31067, hc01, hc12, hlam, hphi, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h30701, h31061, h31067, h31069, hc01, hc12, hlam, hphi, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h0, h30701, h31061, h31067, h31069, hc01, hc12, hlam, hphi, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h31059, hlam, p31097_0]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [h31060, hlam, p31097_1]
                          · have p31097_0 := h31097c.1
                            have p31097_1 := h31097c.2.1
                            have p31097_2 := h31097c.2.2.1
                            have p31097_3 := h31097c.2.2.2
                            linarith only [hlam, p31097_0]
                      · linarith only [h30132, h31060, h31069, hlam]
                    · linarith only [h22350, h31059, h31068, hlam]
                  · linarith only [h22350, h31058, h31067, hlam]
                · linarith only [h18443, h22350, h31058, h31060, h31066, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h15532, h22350, h31059, h31061, h31065, hc01, hc12, hlam, hphi]
            · linarith only [h22350, h31058, h31061, h31064, hlam]
          · linarith only [h0, h22350, h31061, h31063, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h22350, h31061, h31062, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h31131 | h31131
        · linarith only [h0, h30132, h31061, h31131, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h31133 | h31133
          · linarith only [h0, h30701, h31061, h31133, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h31135 | h31135
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31136 | h31136
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31137 | h31137
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31138 | h31138
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31139 | h31139
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31140 | h31140
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31141 | h31141
                        · rcases h0bigk with h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c | h31142c
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [hlam, p31142_0]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [h0, hlam, p31142_1]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [h15532, hlam, p31142_0]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [h18443, hlam, p31142_1]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [h20697, hlam, p31142_1]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [h0, h31133, h31138, h31140, hc01, hc23, hlam, hphi, ht12, p31142_1]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [hlam, p31142_0]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [h22350, hlam, p31142_0]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [h30132, hlam, p31142_1]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [h30701, hlam, p31142_0]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            rcases p31142_3 (m.d 0 1) (by simp) with h31153 | h31153
                            · linarith only [h15532, h31153, hlam]
                            · rcases p31142_3 (m.d 0 2) (by simp) with h31155 | h31155
                              · linarith only [h22350, h31155, hlam]
                              · linarith only [h0, h31155, hlam]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            rcases p31142_3 (m.d 0 1) (by simp) with h31158 | h31158
                            · linarith only [h15532, h31158, hlam]
                            · rcases p31142_3 (m.d 0 2) (by simp) with h31160 | h31160
                              · linarith only [h22350, h31160, hlam]
                              · rcases p31142_3 (m.d 0 3) (by simp) with h31162 | h31162
                                · rcases p31142_3 (m.d 0 4) (by simp) with h31163 | h31163
                                  · linarith only [h31058, h31163, hlam]
                                  · linarith only [h30132, h31163, hlam]
                                · linarith only [h22350, h31162, hlam]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [hlam, p31142_0]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            rcases p31142_3 (m.d 0 1) (by simp) with h31168 | h31168
                            · linarith only [h15532, h31168, hlam]
                            · rcases p31142_3 (m.d 0 2) (by simp) with h31170 | h31170
                              · linarith only [h22350, h31170, hlam]
                              · rcases p31142_3 (m.d 0 3) (by simp) with h31172 | h31172
                                · rcases p31142_3 (m.d 0 4) (by simp) with h31173 | h31173
                                  · linarith only [h31058, h31173, hlam]
                                  · rcases p31142_3 (m.d 0 5) (by simp) with h31175 | h31175
                                    · linarith only [h31059, h31175, hlam]
                                    · rcases h2bigk with h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c | h31177c
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [hlam, p31177_0]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h0, hlam, p31177_1]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h22350, hlam, p31177_0]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h30132, hlam, p31177_0]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h30701, hlam, p31177_0]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h31133, h31138, h31140, hc02, hc23, hlam, hphi, p31177_1]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [hlam, p31177_0]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h31061, hlam, p31177_0]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h31131, hlam, p31177_0]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h31133, hlam, p31177_0]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        rcases p31177_3 (m.d 0 2) (by simp) with h31188 | h31188
                                        · linarith only [h31188, hlam, p31177_0]
                                        · rcases p31177_3 (m.d 1 2) (by simp) with h31190 | h31190
                                          · linarith only [h31061, h31190, hlam]
                                          · linarith only [h0, h31190, hlam]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p31177_1]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [hlam, p31177_0]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h0, h30132, hc01, hc23, hlam, hphi, ht12, p31177_1]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h0, h31133, hc01, hc23, hlam, hphi, ht12, p31177_1]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        rcases p31177_3 (m.d 0 2) (by simp) with h31197 | h31197
                                        · linarith only [h31197, hlam, p31177_0]
                                        · rcases p31177_3 (m.d 1 2) (by simp) with h31199 | h31199
                                          · linarith only [h31131, h31199, hlam]
                                          · linarith only [h0, h31199, hlam]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p31177_1]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h31138, hlam, p31177_1]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [hlam, p31177_0]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h0, h31133, h31138, hc01, hc23, hlam, hphi, ht12, p31177_1]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        rcases p31177_3 (m.d 0 2) (by simp) with h31206 | h31206
                                        · linarith only [h31206, hlam, p31177_0]
                                        · rcases p31177_3 (m.d 1 2) (by simp) with h31208 | h31208
                                          · linarith only [h31133, h31208, hlam]
                                          · linarith only [h0, h31208, hlam]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p31177_1]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h31139, hlam, p31177_1]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [h31140, hlam, p31177_0]
                                      · have p31177_0 := h31177c.1
                                        have p31177_1 := h31177c.2.1
                                        have p31177_2 := h31177c.2.2.1
                                        have p31177_3 := h31177c.2.2.2
                                        linarith only [hlam, p31177_0]
                                · linarith only [h31058, h31172, hlam]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            rcases p31142_3 (m.d 0 1) (by simp) with h31216 | h31216
                            · linarith only [h15532, h31216, hlam]
                            · rcases p31142_3 (m.d 0 2) (by simp) with h31218 | h31218
                              · linarith only [h22350, h31218, hlam]
                              · rcases p31142_3 (m.d 0 3) (by simp) with h31220 | h31220
                                · rcases p31142_3 (m.d 0 4) (by simp) with h31221 | h31221
                                  · linarith only [h31058, h31221, hlam]
                                  · linarith only [h31060, h31221, hlam]
                                · linarith only [h31059, h31220, hlam]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            rcases p31142_3 (m.d 0 1) (by simp) with h31225 | h31225
                            · linarith only [h18443, h31225, hlam]
                            · rcases p31142_3 (m.d 0 2) (by simp) with h31227 | h31227
                              · linarith only [h30132, h31227, hlam]
                              · linarith only [h0, h31227, hlam]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            rcases p31142_3 (m.d 0 1) (by simp) with h31230 | h31230
                            · linarith only [h18443, h31230, hlam]
                            · rcases p31142_3 (m.d 0 2) (by simp) with h31232 | h31232
                              · linarith only [h30132, h31232, hlam]
                              · rcases p31142_3 (m.d 0 3) (by simp) with h31234 | h31234
                                · rcases p31142_3 (m.d 0 4) (by simp) with h31235 | h31235
                                  · rcases p31142_3 (m.d 0 5) (by simp) with h31236 | h31236
                                    · linarith only [h31060, h31236, hlam]
                                    · linarith only [h30701, h31236, hlam]
                                  · linarith only [h30132, h31235, hlam]
                                · linarith only [h22350, h31234, hlam]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [h31058, hlam, p31142_0]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [hlam, p31142_0]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            rcases p31142_3 (m.d 0 1) (by simp) with h31243 | h31243
                            · linarith only [h18443, h31243, hlam]
                            · rcases p31142_3 (m.d 0 2) (by simp) with h31245 | h31245
                              · linarith only [h30132, h31245, hlam]
                              · rcases p31142_3 (m.d 0 3) (by simp) with h31247 | h31247
                                · rcases p31142_3 (m.d 0 4) (by simp) with h31248 | h31248
                                  · rcases p31142_3 (m.d 0 5) (by simp) with h31249 | h31249
                                    · linarith only [h31060, h31249, hlam]
                                    · rcases h2bigk with h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c | h31251c
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [hlam, p31251_0]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h0, hlam, p31251_1]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h22350, hlam, p31251_0]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h30132, hlam, p31251_0]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h30701, hlam, p31251_0]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h0, h31061, hc01, hc23, hlam, hphi, ht12, p31251_1]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [hlam, p31251_0]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h31061, hlam, p31251_0]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h31131, hlam, p31251_0]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h31133, hlam, p31251_0]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        rcases p31251_3 (m.d 0 2) (by simp) with h31262 | h31262
                                        · linarith only [h31262, hlam, p31251_0]
                                        · rcases p31251_3 (m.d 1 2) (by simp) with h31264 | h31264
                                          · linarith only [h31061, h31264, hlam]
                                          · linarith only [h0, h31264, hlam]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p31251_1]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [hlam, p31251_0]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h0, h30132, hc01, hc23, hlam, hphi, ht12, p31251_1]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h0, h30701, hc01, hc23, hlam, hphi, ht12, p31251_1]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        rcases p31251_3 (m.d 0 2) (by simp) with h31271 | h31271
                                        · linarith only [h31271, hlam, p31251_0]
                                        · rcases p31251_3 (m.d 1 2) (by simp) with h31273 | h31273
                                          · linarith only [h31131, h31273, hlam]
                                          · linarith only [h0, h31273, hlam]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p31251_1]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h31138, hlam, p31251_1]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [hlam, p31251_0]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h0, h31133, h31138, hc01, hc23, hlam, hphi, ht12, p31251_1]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        rcases p31251_3 (m.d 0 2) (by simp) with h31280 | h31280
                                        · linarith only [h31280, hlam, p31251_0]
                                        · rcases p31251_3 (m.d 1 2) (by simp) with h31282 | h31282
                                          · linarith only [h31133, h31282, hlam]
                                          · linarith only [h0, h31282, hlam]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p31251_1]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h31139, hlam, p31251_1]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [h31140, hlam, p31251_0]
                                      · have p31251_0 := h31251c.1
                                        have p31251_1 := h31251c.2.1
                                        have p31251_2 := h31251c.2.2.1
                                        have p31251_3 := h31251c.2.2.2
                                        linarith only [hlam, p31251_0]
                                  · linarith only [h31060, h31248, hlam]
                                · linarith only [h31059, h31247, hlam]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            rcases p31142_3 (m.d 0 1) (by simp) with h31291 | h31291
                            · linarith only [h20697, h31291, hlam]
                            · rcases p31142_3 (m.d 0 2) (by simp) with h31293 | h31293
                              · linarith only [h30701, h31293, hlam]
                              · linarith only [h0, h31293, hlam]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            rcases p31142_3 (m.d 0 1) (by simp) with h31296 | h31296
                            · linarith only [h20697, h31296, hlam]
                            · rcases p31142_3 (m.d 0 2) (by simp) with h31298 | h31298
                              · linarith only [h30701, h31298, hlam]
                              · rcases p31142_3 (m.d 0 3) (by simp) with h31300 | h31300
                                · rcases p31142_3 (m.d 0 4) (by simp) with h31301 | h31301
                                  · rcases p31142_3 (m.d 0 5) (by simp) with h31302 | h31302
                                    · rcases h2bigk with h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c | h31303c
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [hlam, p31303_0]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h0, hlam, p31303_1]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h22350, hlam, p31303_0]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h30132, hlam, p31303_0]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h30701, hlam, p31303_0]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h0, h31061, hc01, hc23, hlam, hphi, ht12, p31303_1]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [hlam, p31303_0]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h31061, hlam, p31303_0]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h31131, hlam, p31303_0]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h31133, hlam, p31303_0]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        rcases p31303_3 (m.d 0 2) (by simp) with h31314 | h31314
                                        · linarith only [h31314, hlam, p31303_0]
                                        · rcases p31303_3 (m.d 1 2) (by simp) with h31316 | h31316
                                          · linarith only [h31061, h31316, hlam]
                                          · linarith only [h0, h31316, hlam]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p31303_1]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [hlam, p31303_0]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h18443, h31131, hc01, hc23, hlam, hphi, ht12, p31303_1]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h0, h20697, h31133, hc01, hc23, hlam, hphi, ht12, p31142_1, p31303_1]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        rcases p31303_3 (m.d 0 2) (by simp) with h31323 | h31323
                                        · linarith only [h31323, hlam, p31303_0]
                                        · rcases p31303_3 (m.d 1 2) (by simp) with h31325 | h31325
                                          · linarith only [h31131, h31325, hlam]
                                          · linarith only [h0, h31325, hlam]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p31303_1]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h31138, hlam, p31303_1]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [hlam, p31303_0]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h0, h20697, h31133, h31138, hc01, hc23, hlam, hphi, ht12, p31142_1, p31303_1]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        rcases p31303_3 (m.d 0 2) (by simp) with h31332 | h31332
                                        · linarith only [h31332, hlam, p31303_0]
                                        · rcases p31303_3 (m.d 1 2) (by simp) with h31334 | h31334
                                          · linarith only [h31133, h31334, hlam]
                                          · linarith only [h0, h31334, hlam]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p31303_1]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h31139, hlam, p31303_1]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [h31140, hlam, p31303_0]
                                      · have p31303_0 := h31303c.1
                                        have p31303_1 := h31303c.2.1
                                        have p31303_2 := h31303c.2.2.1
                                        have p31303_3 := h31303c.2.2.2
                                        linarith only [hlam, p31303_0]
                                    · linarith only [h30701, h31302, hlam]
                                  · linarith only [h30132, h31301, hlam]
                                · linarith only [h22350, h31300, hlam]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [h31059, hlam, p31142_0]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [h31060, hlam, p31142_1]
                          · have p31142_0 := h31142c.1
                            have p31142_1 := h31142c.2.1
                            have p31142_2 := h31142c.2.2.1
                            have p31142_3 := h31142c.2.2.2
                            linarith only [hlam, p31142_0]
                        · rcases h0bigk with h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c | h31347c
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [hlam, p31347_0]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h0, hlam, p31347_1]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h15532, hlam, p31347_0]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h18443, hlam, p31347_1]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h20697, hlam, p31347_1]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h22350, hc01, hc23, hlam, hphi, ht12, p31347_1]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [hlam, p31347_0]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h22350, hlam, p31347_0]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h30132, hlam, p31347_1]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h30701, hlam, p31347_0]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            rcases p31347_3 (m.d 0 1) (by simp) with h31358 | h31358
                            · linarith only [h15532, h31358, hlam]
                            · rcases p31347_3 (m.d 0 2) (by simp) with h31360 | h31360
                              · linarith only [h22350, h31360, hlam]
                              · linarith only [h0, h31360, hlam]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            rcases p31347_3 (m.d 0 1) (by simp) with h31363 | h31363
                            · linarith only [h15532, h31363, hlam]
                            · rcases p31347_3 (m.d 0 2) (by simp) with h31365 | h31365
                              · linarith only [h22350, h31365, hlam]
                              · rcases p31347_3 (m.d 0 3) (by simp) with h31367 | h31367
                                · rcases p31347_3 (m.d 0 4) (by simp) with h31368 | h31368
                                  · linarith only [h31058, h31368, hlam]
                                  · linarith only [h30132, h31368, hlam]
                                · linarith only [h22350, h31367, hlam]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [hlam, p31347_0]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h15532, h31060, h31061, h31141, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p31347_1]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            rcases p31347_3 (m.d 0 1) (by simp) with h31374 | h31374
                            · linarith only [h15532, h31374, hlam]
                            · rcases p31347_3 (m.d 0 2) (by simp) with h31376 | h31376
                              · linarith only [h22350, h31376, hlam]
                              · rcases p31347_3 (m.d 0 3) (by simp) with h31378 | h31378
                                · rcases p31347_3 (m.d 0 4) (by simp) with h31379 | h31379
                                  · linarith only [h31058, h31379, hlam]
                                  · linarith only [h31060, h31379, hlam]
                                · linarith only [h31059, h31378, hlam]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            rcases p31347_3 (m.d 0 1) (by simp) with h31383 | h31383
                            · linarith only [h18443, h31383, hlam]
                            · rcases p31347_3 (m.d 0 2) (by simp) with h31385 | h31385
                              · linarith only [h30132, h31385, hlam]
                              · linarith only [h0, h31385, hlam]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            rcases p31347_3 (m.d 0 1) (by simp) with h31388 | h31388
                            · linarith only [h18443, h31388, hlam]
                            · rcases p31347_3 (m.d 0 2) (by simp) with h31390 | h31390
                              · linarith only [h30132, h31390, hlam]
                              · rcases p31347_3 (m.d 0 3) (by simp) with h31392 | h31392
                                · rcases p31347_3 (m.d 0 4) (by simp) with h31393 | h31393
                                  · rcases p31347_3 (m.d 0 5) (by simp) with h31394 | h31394
                                    · linarith only [h31060, h31394, hlam]
                                    · linarith only [h30701, h31394, hlam]
                                  · linarith only [h30132, h31393, hlam]
                                · linarith only [h22350, h31392, hlam]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h31058, hlam, p31347_0]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [hlam, p31347_0]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            rcases p31347_3 (m.d 0 1) (by simp) with h31401 | h31401
                            · linarith only [h18443, h31401, hlam]
                            · rcases p31347_3 (m.d 0 2) (by simp) with h31403 | h31403
                              · linarith only [h30132, h31403, hlam]
                              · rcases p31347_3 (m.d 0 3) (by simp) with h31405 | h31405
                                · rcases p31347_3 (m.d 0 4) (by simp) with h31406 | h31406
                                  · rcases p31347_3 (m.d 0 5) (by simp) with h31407 | h31407
                                    · linarith only [h31060, h31407, hlam]
                                    · rcases h2bigk with h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c | h31409c
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [hlam, p31409_0]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h0, hlam, p31409_1]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h22350, hlam, p31409_0]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h30132, hlam, p31409_0]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h30701, hlam, p31409_0]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h0, h31061, hc01, hc23, hlam, hphi, ht12, p31409_1]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [hlam, p31409_0]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h31061, hlam, p31409_0]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h31131, hlam, p31409_0]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h31133, hlam, p31409_0]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        rcases p31409_3 (m.d 0 2) (by simp) with h31420 | h31420
                                        · linarith only [h31420, hlam, p31409_0]
                                        · rcases p31409_3 (m.d 1 2) (by simp) with h31422 | h31422
                                          · linarith only [h31061, h31422, hlam]
                                          · linarith only [h0, h31422, hlam]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p31409_1]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [hlam, p31409_0]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h18443, h31131, hc01, hc23, hlam, hphi, ht12, p31409_1]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h0, h30701, hc01, hc23, hlam, hphi, ht12, p31409_1]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        rcases p31409_3 (m.d 0 2) (by simp) with h31429 | h31429
                                        · linarith only [h31429, hlam, p31409_0]
                                        · rcases p31409_3 (m.d 1 2) (by simp) with h31431 | h31431
                                          · linarith only [h31131, h31431, hlam]
                                          · linarith only [h0, h31431, hlam]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p31409_1]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h31138, hlam, p31409_1]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [hlam, p31409_0]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h0, h31133, h31138, hc01, hc23, hlam, hphi, ht12, p31409_1]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        rcases p31409_3 (m.d 0 2) (by simp) with h31438 | h31438
                                        · linarith only [h31438, hlam, p31409_0]
                                        · rcases p31409_3 (m.d 1 2) (by simp) with h31440 | h31440
                                          · linarith only [h31133, h31440, hlam]
                                          · linarith only [h0, h31440, hlam]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p31409_1]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h31139, hlam, p31409_1]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [h31140, hlam, p31409_0]
                                      · have p31409_0 := h31409c.1
                                        have p31409_1 := h31409c.2.1
                                        have p31409_2 := h31409c.2.2.1
                                        have p31409_3 := h31409c.2.2.2
                                        linarith only [hlam, p31409_0]
                                  · linarith only [h31060, h31406, hlam]
                                · linarith only [h31059, h31405, hlam]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            rcases p31347_3 (m.d 0 1) (by simp) with h31449 | h31449
                            · linarith only [h20697, h31449, hlam]
                            · rcases p31347_3 (m.d 0 2) (by simp) with h31451 | h31451
                              · linarith only [h30701, h31451, hlam]
                              · linarith only [h0, h31451, hlam]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            rcases p31347_3 (m.d 0 1) (by simp) with h31454 | h31454
                            · linarith only [h20697, h31454, hlam]
                            · rcases p31347_3 (m.d 0 2) (by simp) with h31456 | h31456
                              · linarith only [h30701, h31456, hlam]
                              · rcases p31347_3 (m.d 0 3) (by simp) with h31458 | h31458
                                · rcases p31347_3 (m.d 0 4) (by simp) with h31459 | h31459
                                  · rcases p31347_3 (m.d 0 5) (by simp) with h31460 | h31460
                                    · rcases h2bigk with h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c | h31461c
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [hlam, p31461_0]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h0, hlam, p31461_1]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h22350, hlam, p31461_0]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h30132, hlam, p31461_0]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h30701, hlam, p31461_0]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h0, h31061, hc01, hc23, hlam, hphi, ht12, p31461_1]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [hlam, p31461_0]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h31061, hlam, p31461_0]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h31131, hlam, p31461_0]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h31133, hlam, p31461_0]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        rcases p31461_3 (m.d 0 2) (by simp) with h31472 | h31472
                                        · linarith only [h31472, hlam, p31461_0]
                                        · rcases p31461_3 (m.d 1 2) (by simp) with h31474 | h31474
                                          · linarith only [h31061, h31474, hlam]
                                          · linarith only [h0, h31474, hlam]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p31461_1]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [hlam, p31461_0]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h18443, h31131, hc01, hc23, hlam, hphi, ht12, p31461_1]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h0, h20697, h31133, hc01, hc23, hlam, hphi, ht12, p31347_1, p31461_1]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        rcases p31461_3 (m.d 0 2) (by simp) with h31481 | h31481
                                        · linarith only [h31481, hlam, p31461_0]
                                        · rcases p31461_3 (m.d 1 2) (by simp) with h31483 | h31483
                                          · linarith only [h31131, h31483, hlam]
                                          · linarith only [h0, h31483, hlam]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p31461_1]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h31138, hlam, p31461_1]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [hlam, p31461_0]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h0, h20697, h31133, h31138, hc01, hc23, hlam, hphi, ht12, p31347_1, p31461_1]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        rcases p31461_3 (m.d 0 2) (by simp) with h31490 | h31490
                                        · linarith only [h31490, hlam, p31461_0]
                                        · rcases p31461_3 (m.d 1 2) (by simp) with h31492 | h31492
                                          · linarith only [h31133, h31492, hlam]
                                          · linarith only [h0, h31492, hlam]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p31461_1]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h31139, hlam, p31461_1]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [h31140, hlam, p31461_0]
                                      · have p31461_0 := h31461c.1
                                        have p31461_1 := h31461c.2.1
                                        have p31461_2 := h31461c.2.2.1
                                        have p31461_3 := h31461c.2.2.2
                                        linarith only [hlam, p31461_0]
                                    · linarith only [h30701, h31460, hlam]
                                  · linarith only [h30132, h31459, hlam]
                                · linarith only [h22350, h31458, hlam]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h31059, hlam, p31347_0]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [h31060, hlam, p31347_1]
                          · have p31347_0 := h31347c.1
                            have p31347_1 := h31347c.2.1
                            have p31347_2 := h31347c.2.2.1
                            have p31347_3 := h31347c.2.2.2
                            linarith only [hlam, p31347_0]
                      · linarith only [h30132, h31060, h31140, hlam]
                    · linarith only [h15532, h31059, h31061, h31139, hlam]
                  · linarith only [h15532, h31058, h31061, h31138, hlam]
                · linarith only [h15532, h18443, h31058, h31060, h31061, h31137, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h15532, h31059, h31136, hlam]
            · linarith only [h15532, h31058, h31135, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h31511 | h31511
      · rcases m.htr 1 2 4 (by decide) (by decide) with h31512 | h31512
        · rcases m.htr 1 2 5 (by decide) (by decide) with h31513 | h31513
          · rcases m.htr 1 3 4 (by decide) (by decide) with h31514 | h31514
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31515 | h31515
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31516 | h31516
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31517 | h31517
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31518 | h31518
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31519 | h31519
                      · linarith only [h0, h30132, h31060, h31511, h31517, h31519, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h30132, h31514, h31516, h31519, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h15532, h22350, h31059, h31511, h31518, hc01, hc12, hlam, hphi]
                  · linarith only [h22350, h31058, h31517, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31524 | h31524
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31525 | h31525
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31526 | h31526
                      · linarith only [h18443, h31060, h31512, h31526, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31528 | h31528
                        · linarith only [h18443, h31516, h31528, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c | h31530c
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [hlam, p31530_0]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h0, hlam, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h15532, hlam, p31530_0]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h18443, hlam, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h20697, hlam, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h30132, h31512, hc01, hc14, hlam, hphi, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [hlam, p31530_0]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h22350, hlam, p31530_0]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h30132, hlam, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h30701, hlam, p31530_0]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h22350, h31511, hc01, hc12, hlam, hphi, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h0, h22350, h31511, hc01, hc12, hlam, hphi, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [hlam, p31530_0]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h0, h22350, h30132, h31511, hc01, hc12, hlam, hphi, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h0, h22350, h30132, h31060, h31511, hc01, hc12, hlam, hphi, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h18443, h31516, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h0, h30132, h31512, h31516, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h31058, hlam, p31530_0]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [hlam, p31530_0]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h31060, hlam, p31530_0]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h22350, h31059, h31511, hc01, hc12, hlam, hphi, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h0, h22350, h31059, h31511, hc01, hc12, hlam, hphi, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h31059, hlam, p31530_0]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [h18443, h22350, h31059, h31511, hc01, hc12, hlam, hphi, p31530_1]
                          · have p31530_0 := h31530c.1
                            have p31530_1 := h31530c.2.1
                            have p31530_2 := h31530c.2.2.1
                            have p31530_3 := h31530c.2.2.2
                            linarith only [hlam, p31530_0]
                    · linarith only [h22350, h31059, h31525, hlam]
                  · linarith only [h0, h18443, h22350, h31058, h31516, h31524, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h15532, h31059, h31515, hlam]
            · linarith only [h22350, h31058, h31511, h31514, hlam]
          · linarith only [h0, h22350, h31511, h31513, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h22350, h31511, h31512, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h31562 | h31562
        · linarith only [h0, h30132, h31511, h31562, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h31564 | h31564
          · linarith only [h0, h30701, h31511, h31564, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h31566 | h31566
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31567 | h31567
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31568 | h31568
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31569 | h31569
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31570 | h31570
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31571 | h31571
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31572 | h31572
                        · linarith only [h0, h15532, h30132, h31058, h31060, h31572, hc01, hc13, hlam, hphi]
                        · rcases h0bigk with h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c | h31574c
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [hlam, p31574_0]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h0, hlam, p31574_1]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h15532, hlam, p31574_0]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h18443, hlam, p31574_1]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h20697, hlam, p31574_1]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h30132, h31060, h31568, hc01, hc14, hlam, hphi, p31574_1]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [hlam, p31574_0]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h22350, hlam, p31574_0]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h30132, hlam, p31574_1]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h30701, hlam, p31574_0]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            rcases p31574_3 (m.d 0 1) (by simp) with h31585 | h31585
                            · linarith only [h15532, h31585, hlam]
                            · rcases p31574_3 (m.d 0 2) (by simp) with h31587 | h31587
                              · linarith only [h22350, h31587, hlam]
                              · linarith only [h0, h31587, hlam]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            rcases p31574_3 (m.d 0 1) (by simp) with h31590 | h31590
                            · linarith only [h15532, h31590, hlam]
                            · rcases p31574_3 (m.d 0 2) (by simp) with h31592 | h31592
                              · linarith only [h22350, h31592, hlam]
                              · rcases p31574_3 (m.d 0 3) (by simp) with h31594 | h31594
                                · rcases p31574_3 (m.d 0 4) (by simp) with h31595 | h31595
                                  · linarith only [h31058, h31595, hlam]
                                  · linarith only [h30132, h31595, hlam]
                                · linarith only [h22350, h31594, hlam]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [hlam, p31574_0]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            rcases p31574_3 (m.d 0 1) (by simp) with h31600 | h31600
                            · linarith only [h15532, h31600, hlam]
                            · rcases p31574_3 (m.d 0 2) (by simp) with h31602 | h31602
                              · linarith only [h22350, h31602, hlam]
                              · rcases p31574_3 (m.d 0 3) (by simp) with h31604 | h31604
                                · rcases p31574_3 (m.d 0 4) (by simp) with h31605 | h31605
                                  · linarith only [h31058, h31605, hlam]
                                  · rcases p31574_3 (m.d 0 5) (by simp) with h31607 | h31607
                                    · linarith only [h31059, h31607, hlam]
                                    · linarith only [h31060, h31607, hlam]
                                · linarith only [h31058, h31604, hlam]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            rcases p31574_3 (m.d 0 1) (by simp) with h31611 | h31611
                            · linarith only [h15532, h31611, hlam]
                            · rcases p31574_3 (m.d 0 2) (by simp) with h31613 | h31613
                              · linarith only [h22350, h31613, hlam]
                              · rcases p31574_3 (m.d 0 3) (by simp) with h31615 | h31615
                                · rcases p31574_3 (m.d 0 4) (by simp) with h31616 | h31616
                                  · linarith only [h31058, h31616, hlam]
                                  · rcases p31574_3 (m.d 0 5) (by simp) with h31618 | h31618
                                    · linarith only [h31059, h31618, hlam]
                                    · rcases h2bigk with h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c | h31620c
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [hlam, p31620_0]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h0, hlam, p31620_1]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h22350, hlam, p31620_0]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h30132, hlam, p31620_0]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h30701, hlam, p31620_0]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h31564, h31569, h31571, hc02, hc23, hlam, hphi, p31620_1]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [hlam, p31620_0]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h31511, hlam, p31620_0]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h31562, hlam, p31620_0]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h31564, hlam, p31620_0]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        rcases p31620_3 (m.d 0 2) (by simp) with h31631 | h31631
                                        · linarith only [h31631, hlam, p31620_0]
                                        · rcases p31620_3 (m.d 1 2) (by simp) with h31633 | h31633
                                          · linarith only [h31511, h31633, hlam]
                                          · linarith only [h0, h31633, hlam]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p31620_1]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [hlam, p31620_0]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h18443, h31562, hc01, hc23, hlam, hphi, ht12, p31620_1]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h0, h31564, hc01, hc23, hlam, hphi, ht12, p31620_1]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        rcases p31620_3 (m.d 0 2) (by simp) with h31640 | h31640
                                        · linarith only [h31640, hlam, p31620_0]
                                        · rcases p31620_3 (m.d 1 2) (by simp) with h31642 | h31642
                                          · linarith only [h31562, h31642, hlam]
                                          · linarith only [h0, h31642, hlam]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p31620_1]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h31569, hlam, p31620_1]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [hlam, p31620_0]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h0, h31564, h31569, hc01, hc23, hlam, hphi, ht12, p31620_1]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        rcases p31620_3 (m.d 0 2) (by simp) with h31649 | h31649
                                        · linarith only [h31649, hlam, p31620_0]
                                        · rcases p31620_3 (m.d 1 2) (by simp) with h31651 | h31651
                                          · linarith only [h31564, h31651, hlam]
                                          · linarith only [h0, h31651, hlam]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p31620_1]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h31570, hlam, p31620_1]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [h31571, hlam, p31620_0]
                                      · have p31620_0 := h31620c.1
                                        have p31620_1 := h31620c.2.1
                                        have p31620_2 := h31620c.2.2.1
                                        have p31620_3 := h31620c.2.2.2
                                        linarith only [hlam, p31620_0]
                                · linarith only [h31059, h31615, hlam]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h31060, h31568, hc01, hc14, hlam, hphi, p31574_1]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h0, h31060, h31568, hc01, hc14, hlam, hphi, p31574_1]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h31058, hlam, p31574_0]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [hlam, p31574_0]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h31060, hlam, p31574_0]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h31060, h31568, hc01, hc14, hlam, hphi, p31574_1]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h0, h31060, h31568, hc01, hc14, hlam, hphi, p31574_1]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h31059, hlam, p31574_0]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [h18443, h31060, h31568, hc01, hc14, hlam, hphi, p31574_1]
                          · have p31574_0 := h31574c.1
                            have p31574_1 := h31574c.2.1
                            have p31574_2 := h31574c.2.2.1
                            have p31574_3 := h31574c.2.2.2
                            linarith only [hlam, p31574_0]
                      · linarith only [h31562, h31568, h31571, hlam]
                    · linarith only [h31059, h31060, h31562, h31568, h31569, h31570, hlam]
                  · linarith only [h15532, h31058, h31511, h31569, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31672 | h31672
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31673 | h31673
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31674 | h31674
                      · linarith only [h18443, h31568, h31672, h31674, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h31562, h31674, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h15532, h22350, h31059, h31673, hc01, hc13, hlam, hphi]
                  · linarith only [h15532, h18443, h31058, h31511, h31568, h31672, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h15532, h31059, h31567, hlam]
            · linarith only [h15532, h31058, h31566, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h31681 | h31681
    · linarith only [h31058, h31059, h31681, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h31683 | h31683
      · rcases m.htr 1 2 4 (by decide) (by decide) with h31684 | h31684
        · rcases m.htr 1 2 5 (by decide) (by decide) with h31685 | h31685
          · rcases m.htr 1 3 4 (by decide) (by decide) with h31686 | h31686
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31687 | h31687
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31688 | h31688
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31689 | h31689
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31690 | h31690
                    · linarith only [h31058, h31059, h31683, h31690, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h22350, h31687, h31690, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h22350, h31058, h31059, h31683, h31687, h31689, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31694 | h31694
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31695 | h31695
                    · linarith only [h31058, h31059, h31683, h31695, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h22350, h31683, h31687, h31695, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h15532, h22350, h31058, h31683, h31694, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31699 | h31699
                · linarith only [h18443, h31681, h31686, h31687, h31699, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31701 | h31701
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31702 | h31702
                    · linarith only [h31683, h31687, h31702, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31704 | h31704
                      · linarith only [h20697, h31684, h31699, h31704, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31706 | h31706
                        · linarith only [h18443, h31699, h31706, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c | h31708c
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [hlam, p31708_0]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h0, hlam, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h15532, hlam, p31708_0]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h18443, hlam, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h20697, hlam, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h30132, h31684, hc01, hc14, hlam, hphi, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [hlam, p31708_0]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h22350, hlam, p31708_0]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h30132, hlam, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h30701, hlam, p31708_0]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h22350, h31683, h31687, h31706, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h22350, h31683, h31687, h31706, hc02, hc45, hlam, hphi, ht23, ht34, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [hlam, p31708_0]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h22350, h31683, h31687, h31706, hc04, hc45, hlam, hphi, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h31059, hlam, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h22350, h31058, h31683, h31687, h31706, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h0, h22350, h31058, h31683, h31687, h31706, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h31058, hlam, p31708_0]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [hlam, p31708_0]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h31681, hlam, p31708_0]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h30701, h31685, hc01, hc12, hlam, hphi, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h0, h30701, h31685, hc01, hc12, hlam, hphi, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h31058, h31059, h31706, hc34, hc45, hlam, hphi, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [h0, h30132, h30701, h31685, hc01, hc12, hlam, hphi, p31708_1]
                          · have p31708_0 := h31708c.1
                            have p31708_1 := h31708c.2.1
                            have p31708_2 := h31708c.2.2.1
                            have p31708_3 := h31708c.2.2.2
                            linarith only [hlam, p31708_0]
                  · linarith only [h0, h15532, h22350, h31058, h31701, hc01, hc13, hlam, hphi]
            · linarith only [h15532, h31058, h31686, hlam]
          · linarith only [h0, h22350, h31683, h31685, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h22350, h31683, h31684, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h31738 | h31738
        · linarith only [h0, h30132, h31683, h31738, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h31740 | h31740
          · linarith only [h0, h30701, h31683, h31740, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h31742 | h31742
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31743 | h31743
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31744 | h31744
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31745 | h31745
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31746 | h31746
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31747 | h31747
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31748 | h31748
                        · linarith only [h0, h30132, h31058, h31059, h31681, h31683, h31743, h31748, hc01, hc23, hlam, hphi, ht12]
                        · rcases h0bigk with h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c | h31750c
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [hlam, p31750_0]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h0, hlam, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h15532, hlam, p31750_0]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h18443, hlam, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h20697, hlam, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h0, h31740, h31745, h31747, hc01, hc23, hlam, hphi, ht12, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [hlam, p31750_0]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h22350, hlam, p31750_0]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h30132, hlam, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h30701, hlam, p31750_0]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h31059, h31683, h31742, h31744, h31748, hc01, hc23, hlam, hphi, ht12, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h31059, h31683, h31742, h31744, h31748, hc02, hc23, hlam, hphi, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [hlam, p31750_0]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h0, h30132, h31059, h31683, h31742, h31744, h31748, hc01, hc23, hlam, hphi, ht12, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h31059, hlam, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h31058, h31059, h31683, h31742, h31744, h31748, hc01, hc23, hlam, hphi, ht12, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h0, h31058, h31059, h31683, h31742, h31744, h31748, hc01, hc23, hlam, hphi, ht12, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h31058, hlam, p31750_0]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [hlam, p31750_0]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h31681, hlam, p31750_0]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h31059, h31683, h31742, h31744, h31748, hc01, hc23, hlam, hphi, ht12, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h0, h31059, h31683, h31742, h31744, h31748, hc01, hc23, hlam, hphi, ht12, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h31058, h31059, h31683, h31742, h31744, h31748, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [h18443, h31059, h31683, h31742, h31744, h31748, hc01, hc23, hlam, hphi, ht12, p31750_1]
                          · have p31750_0 := h31750c.1
                            have p31750_1 := h31750c.2.1
                            have p31750_2 := h31750c.2.2.1
                            have p31750_3 := h31750c.2.2.2
                            linarith only [hlam, p31750_0]
                      · linarith only [h0, h30132, h31683, h31742, h31744, h31747, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h30132, h31681, h31683, h31742, h31744, h31746, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h30132, h31058, h31681, h31683, h31742, h31744, h31745, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31779 | h31779
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31780 | h31780
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31781 | h31781
                      · linarith only [h18443, h31744, h31781, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h31738, h31781, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h22350, h31743, h31780, hc01, hc13, hlam, hphi]
                  · linarith only [h15532, h31058, h31683, h31779, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31786 | h31786
                · linarith only [h18443, h31681, h31742, h31743, h31786, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31788 | h31788
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31789 | h31789
                    · linarith only [h15532, h31743, h31789, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h31683, h31789, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h31058, h31683, h31788, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · linarith only [h15532, h31058, h31742, hlam]

end R2N4
