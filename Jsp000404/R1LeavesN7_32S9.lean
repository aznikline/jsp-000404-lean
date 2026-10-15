import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2875 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3145 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3689 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3898 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h4022 | h4022
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4023 | h4023
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4024 | h4024
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4025 | h4025
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4026 | h4026
          · rcases h0bigk with h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c | h4027c
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [hlam, p4027_0]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h0, hlam, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h2352, hlam, p4027_0]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h2875, hlam, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h2994, hlam, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h3145, h4025, hc01, hc12, hlam, hphi, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [hlam, p4027_0]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h3145, hlam, p4027_0]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h3689, hlam, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h3898, hlam, p4027_0]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h2352, hc01, hc13, hlam, hphi, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h3145, h4025, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [hlam, p4027_0]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h3145, h4024, h4025, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4027_1, u4ehi4]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h3145, h4025, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h0, h3689, hc01, hc24, hlam, hphi, ht12, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h4022, hlam, p4027_0]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [hlam, p4027_0]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h0, h3145, h3898, h4022, h4025, hc01, hc12, hlam, hphi, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h2994, h4026, hc01, hc14, hlam, hphi, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h0, h2994, h4026, hc01, hc14, hlam, hphi, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h4023, hlam, p4027_0]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [h4024, hlam, p4027_1]
            · have p4027_0 := h4027c.1
              have p4027_1 := h4027c.2.1
              have p4027_2 := h4027c.2.2.1
              have p4027_3 := h4027c.2.2.2
              linarith only [hlam, p4027_0]
          · linarith only [h2875, h4024, h4026, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4054 | h4054
          · rcases h0bigk with h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [hlam, p4055_0]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h0, hlam, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h2352, hlam, p4055_0]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h2875, hlam, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h2994, hlam, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h0, hc01, hc12, hlam, hphi, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [hlam, p4055_0]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h3145, hlam, p4055_0]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h3689, hlam, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h3898, hlam, p4055_0]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h2352, hc01, hc13, hlam, hphi, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h3145, hc02, hc23, hlam, hphi, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [hlam, p4055_0]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h3145, h4024, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4055_1, u4ehi4]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h2994, h3145, hc01, hc23, hlam, hphi, ht12, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h0, h3689, hc01, hc24, hlam, hphi, ht12, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h4022, hlam, p4055_0]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [hlam, p4055_0]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h0, h3145, h3898, h4022, hc01, hc23, hlam, hphi, ht12, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h2994, h4054, hc01, hc14, hlam, hphi, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h0, h2994, h4054, hc01, hc14, hlam, hphi, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h4023, hlam, p4055_0]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [h4024, hlam, p4055_1]
            · have p4055_0 := h4055c.1
              have p4055_1 := h4055c.2.1
              have p4055_2 := h4055c.2.2.1
              have p4055_3 := h4055c.2.2.2
              linarith only [hlam, p4055_0]
          · linarith only [h2875, h4024, h4054, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4082 | h4082
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4083 | h4083
          · rcases h0bigk with h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c | h4084c
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [hlam, p4084_0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h0, hlam, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h2352, hlam, p4084_0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h2875, hlam, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h2994, hlam, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h3898, hc01, hc25, hlam, hphi, ht12, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [hlam, p4084_0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h3145, hlam, p4084_0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h3689, hlam, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h3898, hlam, p4084_0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h3145, h4082, hc01, hc12, hlam, hphi, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h3145, h4082, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [hlam, p4084_0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h3145, h4082, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4084_1, u4ehi0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h3145, h4082, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h0, h3689, hc01, hc24, hlam, hphi, ht12, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h4022, hlam, p4084_0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [hlam, p4084_0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h4024, hlam, p4084_0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h2994, hc01, hc15, hlam, hphi, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h0, h3898, hc01, hc25, hlam, hphi, ht12, p4084_1]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h4023, hlam, p4084_0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [h3145, h4023, h4082, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4084_1, u4ehi0]
            · have p4084_0 := h4084c.1
              have p4084_1 := h4084c.2.1
              have p4084_2 := h4084c.2.2.1
              have p4084_3 := h4084c.2.2.2
              linarith only [hlam, p4084_0]
          · rcases h0bigk with h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [hlam, p4110_0]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h0, hlam, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h2352, hlam, p4110_0]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h2875, hlam, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h2994, hlam, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h0, hc01, hc12, hlam, hphi, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [hlam, p4110_0]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h3145, hlam, p4110_0]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h3689, hlam, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h3898, hlam, p4110_0]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h3145, h4082, hc01, hc12, hlam, hphi, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h3145, h4082, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [hlam, p4110_0]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h3145, h4022, h4082, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4110_1, u4ehi3]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h3145, h4082, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h0, h2875, h4083, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h4022, hlam, p4110_0]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [hlam, p4110_0]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h4024, hlam, p4110_0]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h2994, hc01, hc15, hlam, hphi, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h0, h3898, hc01, hc25, hlam, hphi, ht12, p4110_1]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h4023, hlam, p4110_0]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [h3145, h4023, h4082, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4110_1, u4ehi0]
            · have p4110_0 := h4110c.1
              have p4110_1 := h4110c.2.1
              have p4110_2 := h4110c.2.2.1
              have p4110_3 := h4110c.2.2.2
              linarith only [hlam, p4110_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4136 | h4136
          · rcases h0bigk with h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c | h4137c
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [hlam, p4137_0]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h0, hlam, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h2352, hlam, p4137_0]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h2875, hlam, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h2994, hlam, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h0, hc01, hc12, hlam, hphi, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [hlam, p4137_0]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h3145, hlam, p4137_0]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h3689, hlam, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h3898, hlam, p4137_0]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h2352, hc01, hc13, hlam, hphi, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h3145, hc02, hc23, hlam, hphi, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [hlam, p4137_0]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h3145, h4022, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4137_1, u4ehi3]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h2994, h3145, hc01, hc23, hlam, hphi, ht12, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h0, h3689, hc01, hc24, hlam, hphi, ht12, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h4022, hlam, p4137_0]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [hlam, p4137_0]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h4024, hlam, p4137_0]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h2994, h4136, hc01, hc14, hlam, hphi, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h0, h2994, h4136, hc01, hc14, hlam, hphi, p4137_1]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h4023, hlam, p4137_0]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [h4024, h4136, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4137_1, u4ehi0]
            · have p4137_0 := h4137c.1
              have p4137_1 := h4137c.2.1
              have p4137_2 := h4137c.2.2.1
              have p4137_3 := h4137c.2.2.2
              linarith only [hlam, p4137_0]
          · rcases h0bigk with h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c | h4163c
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [hlam, p4163_0]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h0, hlam, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h2352, hlam, p4163_0]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h2875, hlam, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h2994, hlam, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h0, h4082, hc01, hc23, hlam, hphi, ht12, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [hlam, p4163_0]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h3145, hlam, p4163_0]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h3689, hlam, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h3898, hlam, p4163_0]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h2352, h4082, hc01, hc23, hlam, hphi, ht12, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h2352, h4082, hc02, hc23, hlam, hphi, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [hlam, p4163_0]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h2352, h4022, h4082, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4163_1, u4ehi3]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h2352, h2994, h4082, hc01, hc23, hlam, hphi, ht12, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h2875, h4136, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h0, h2875, h4136, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h4022, hlam, p4163_0]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [hlam, p4163_0]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h4024, hlam, p4163_0]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h2994, h4136, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h0, h2994, h4136, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4163_1]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h4023, hlam, p4163_0]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [h2994, h4136, hc45, hlam, hphi, p4163_1, u4ehi0]
            · have p4163_0 := h4163c.1
              have p4163_1 := h4163c.2.1
              have p4163_2 := h4163c.2.2.1
              have p4163_3 := h4163c.2.2.2
              linarith only [hlam, p4163_0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4189 | h4189
      · linarith only [h4022, h4023, h4189, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4191 | h4191
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4192 | h4192
          · rcases h0bigk with h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c | h4193c
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [hlam, p4193_0]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h0, hlam, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h2352, hlam, p4193_0]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h2875, hlam, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h2994, hlam, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h0, hc01, hc12, hlam, hphi, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [hlam, p4193_0]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h3145, hlam, p4193_0]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h3689, hlam, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h3898, hlam, p4193_0]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h4023, hc01, hc35, hlam, hphi, ht12, ht23, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h4023, hc02, hc35, hlam, hphi, ht23, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [hlam, p4193_0]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h4023, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4193_1, u4ehi0]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h4023, hlam, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h0, h3689, hc01, hc24, hlam, hphi, ht12, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h4022, hlam, p4193_0]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [hlam, p4193_0]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h4189, hlam, p4193_0]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h2994, hc01, hc15, hlam, hphi, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h0, h3898, hc01, hc25, hlam, hphi, ht12, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h4023, hc03, hc35, hlam, hphi, p4193_1]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [h4022, h4189, h4192, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4193_1, u4ehi3]
            · have p4193_0 := h4193c.1
              have p4193_1 := h4193c.2.1
              have p4193_2 := h4193c.2.2.1
              have p4193_3 := h4193c.2.2.2
              linarith only [hlam, p4193_0]
          · rcases h0bigk with h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c | h4219c
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [hlam, p4219_0]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h0, hlam, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h2352, hlam, p4219_0]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h2875, hlam, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h2994, hlam, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h0, hc01, hc12, hlam, hphi, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [hlam, p4219_0]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h3145, hlam, p4219_0]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h3689, hlam, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h3898, hlam, p4219_0]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h2352, hc01, hc13, hlam, hphi, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h3145, h4191, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [hlam, p4219_0]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h3145, h4022, h4191, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4219_1, u4ehi3]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h4023, hlam, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h0, h2875, h4192, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h4022, hlam, p4219_0]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [hlam, p4219_0]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h4189, hlam, p4219_0]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h2994, hc01, hc15, hlam, hphi, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h0, h3898, hc01, hc25, hlam, hphi, ht12, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h4023, hc03, hc35, hlam, hphi, p4219_1]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [h4189, hc45, hlam, hphi, p4219_1, u4ehi0]
            · have p4219_0 := h4219c.1
              have p4219_1 := h4219c.2.1
              have p4219_2 := h4219c.2.2.1
              have p4219_3 := h4219c.2.2.2
              linarith only [hlam, p4219_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4245 | h4245
          · rcases h0bigk with h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [hlam, p4246_0]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h0, hlam, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h2352, hlam, p4246_0]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h2875, hlam, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h2994, hlam, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h0, h4191, hc01, hc23, hlam, hphi, ht12, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [hlam, p4246_0]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h3145, hlam, p4246_0]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h3689, hlam, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h3898, hlam, p4246_0]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h2352, h4191, hc01, hc23, hlam, hphi, ht12, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h2352, h4191, hc02, hc23, hlam, hphi, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [hlam, p4246_0]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h2352, h4022, h4191, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4246_1, u4ehi3]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h4023, hlam, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h0, h3689, hc01, hc24, hlam, hphi, ht12, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h4022, hlam, p4246_0]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [hlam, p4246_0]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h4189, hlam, p4246_0]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h4189, h4245, hc01, hc14, hlam, hphi, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h0, h4189, h4245, hc01, hc14, hlam, hphi, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h4189, h4245, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4246_1]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [h4022, h4189, h4245, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4246_1, u4ehi3]
            · have p4246_0 := h4246c.1
              have p4246_1 := h4246c.2.1
              have p4246_2 := h4246c.2.2.1
              have p4246_3 := h4246c.2.2.2
              linarith only [hlam, p4246_0]
          · rcases h0bigk with h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [hlam, p4272_0]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h0, hlam, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h2352, hlam, p4272_0]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h2875, hlam, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h2994, hlam, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h0, h4191, hc01, hc23, hlam, hphi, ht12, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [hlam, p4272_0]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h3145, hlam, p4272_0]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h3689, hlam, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h3898, hlam, p4272_0]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h2352, h4191, hc01, hc23, hlam, hphi, ht12, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h2352, h4191, hc02, hc23, hlam, hphi, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [hlam, p4272_0]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h2352, h4022, h4191, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4272_1, u4ehi3]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h4023, hlam, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h0, h2875, h4245, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h4022, hlam, p4272_0]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [hlam, p4272_0]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h4189, hlam, p4272_0]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h2994, hc01, hc15, hlam, hphi, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h0, h3898, hc01, hc25, hlam, hphi, ht12, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h4023, hc03, hc35, hlam, hphi, p4272_1]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [h4189, hc45, hlam, hphi, p4272_1, u4ehi0]
            · have p4272_0 := h4272c.1
              have p4272_1 := h4272c.2.1
              have p4272_2 := h4272c.2.2.1
              have p4272_3 := h4272c.2.2.2
              linarith only [hlam, p4272_0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4298 | h4298
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4299 | h4299
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4300 | h4300
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4301 | h4301
          · rcases h0bigk with h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c | h4302c
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [hlam, p4302_0]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h0, hlam, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h2352, hlam, p4302_0]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h2875, hlam, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h2994, hlam, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h0, hc01, hc12, hlam, hphi, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [hlam, p4302_0]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h3145, hlam, p4302_0]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h3689, hlam, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h3898, hlam, p4302_0]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h4022, hc01, hc34, hlam, hphi, ht12, ht23, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h4022, hc02, hc34, hlam, hphi, ht23, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [hlam, p4302_0]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h4022, hlam, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h4022, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h0, h3689, hc01, hc24, hlam, hphi, ht12, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h4022, hc03, hc34, hlam, hphi, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [hlam, p4302_0]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h0, h3898, h4022, hc01, hc34, hlam, hphi, ht12, ht23, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h2352, h4298, hc01, hc13, hlam, hphi, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h0, h3145, h4298, h4300, hc01, hc12, hlam, hphi, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h4298, hlam, p4302_0]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [h4299, hlam, p4302_1]
            · have p4302_0 := h4302c.1
              have p4302_1 := h4302c.2.1
              have p4302_2 := h4302c.2.2.1
              have p4302_3 := h4302c.2.2.2
              linarith only [hlam, p4302_0]
          · linarith only [h2875, h4022, h4298, h4299, h4301, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4329 | h4329
          · rcases h0bigk with h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c | h4330c
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [hlam, p4330_0]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h0, hlam, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h2352, hlam, p4330_0]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h2875, hlam, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h2994, hlam, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h0, hc01, hc12, hlam, hphi, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [hlam, p4330_0]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h3145, hlam, p4330_0]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h3689, hlam, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h3898, hlam, p4330_0]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h4022, hc01, hc34, hlam, hphi, ht12, ht23, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h4022, hc02, hc34, hlam, hphi, ht23, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [hlam, p4330_0]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h4022, hlam, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h4022, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h4022, hc01, hc34, hlam, hphi, ht12, ht23, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h0, h4022, hc01, hc34, hlam, hphi, ht12, ht23, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h4022, hc03, hc34, hlam, hphi, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [hlam, p4330_0]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h4022, h4299, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4330_1, u4ehi4]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h2352, h4298, h4300, hc01, hc23, hlam, hphi, ht12, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h0, h2352, h4298, h4300, hc01, hc23, hlam, hphi, ht12, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h4298, hlam, p4330_0]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [h4299, hlam, p4330_1]
            · have p4330_0 := h4330c.1
              have p4330_1 := h4330c.2.1
              have p4330_2 := h4330c.2.2.1
              have p4330_3 := h4330c.2.2.2
              linarith only [hlam, p4330_0]
          · linarith only [h2875, h4299, h4329, hlam]
      · linarith only [h4022, h4298, h4299, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4358 | h4358
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4359 | h4359
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4360 | h4360
          · rcases h0bigk with h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c | h4361c
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [hlam, p4361_0]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h0, hlam, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h2352, hlam, p4361_0]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h2875, hlam, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h2994, hlam, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h0, hc01, hc12, hlam, hphi, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [hlam, p4361_0]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h3145, hlam, p4361_0]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h3689, hlam, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h3898, hlam, p4361_0]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h4022, hc01, hc34, hlam, hphi, ht12, ht23, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h4022, hc02, hc34, hlam, hphi, ht23, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [hlam, p4361_0]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h4022, hlam, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h4298, hlam, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h0, h3689, hc01, hc24, hlam, hphi, ht12, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h4022, hc03, hc34, hlam, hphi, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [hlam, p4361_0]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h0, h3145, h4022, h4298, hc01, hc34, hlam, hphi, ht12, ht23, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h2994, hc01, hc15, hlam, hphi, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h0, h3898, hc01, hc25, hlam, hphi, ht12, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h0, h3145, h4298, hc01, hc35, hlam, hphi, ht12, ht23, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [h4358, hlam, p4361_1]
            · have p4361_0 := h4361c.1
              have p4361_1 := h4361c.2.1
              have p4361_2 := h4361c.2.2.1
              have p4361_3 := h4361c.2.2.2
              linarith only [hlam, p4361_0]
          · linarith only [h2875, h4022, h4358, h4360, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4388 | h4388
          · rcases h0bigk with h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [hlam, p4389_0]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h0, hlam, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h2352, hlam, p4389_0]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h2875, hlam, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h2994, hlam, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h0, h4359, hc01, hc23, hlam, hphi, ht12, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [hlam, p4389_0]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h3145, hlam, p4389_0]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h3689, hlam, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h3898, hlam, p4389_0]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h2352, hc01, hc13, hlam, hphi, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h3145, hc02, hc23, hlam, hphi, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [hlam, p4389_0]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h4022, hlam, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h4298, hlam, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h4022, hc01, hc34, hlam, hphi, ht12, ht23, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h0, h4022, hc01, hc34, hlam, hphi, ht12, ht23, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h4022, hc03, hc34, hlam, hphi, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [hlam, p4389_0]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h2994, h4022, hc01, hc34, hlam, hphi, ht12, ht23, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h2994, h4388, hc01, hc14, hlam, hphi, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h0, h2994, h4388, hc01, hc14, hlam, hphi, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h0, h3145, h4298, hc01, hc35, hlam, hphi, ht12, ht23, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [h4358, hlam, p4389_1]
            · have p4389_0 := h4389c.1
              have p4389_1 := h4389c.2.1
              have p4389_2 := h4389c.2.2.1
              have p4389_3 := h4389c.2.2.2
              linarith only [hlam, p4389_0]
          · linarith only [h2875, h4022, h4358, h4388, hc01, hc34, hlam, hphi, ht12, ht23]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4416 | h4416
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4417 | h4417
          · rcases h0bigk with h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c | h4418c
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [hlam, p4418_0]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h0, hlam, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h2352, hlam, p4418_0]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h2875, hlam, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h2994, hlam, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h3145, hc01, hc23, hlam, hphi, ht12, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [hlam, p4418_0]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h3145, hlam, p4418_0]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h3689, hlam, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h3898, hlam, p4418_0]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h2352, h4416, hc01, hc12, hlam, hphi, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h0, h2352, h4416, hc01, hc12, hlam, hphi, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [hlam, p4418_0]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h4022, hlam, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h4298, hlam, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h4358, h4417, hc01, hc14, hlam, hphi, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h0, h4358, h4417, hc01, hc14, hlam, hphi, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h4358, h4417, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [hlam, p4418_0]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h4358, hlam, p4418_0]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h4358, h4417, hc01, hc14, hlam, hphi, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h0, h4358, h4417, hc01, hc14, hlam, hphi, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h0, h3145, h4358, h4417, hc01, hc14, hlam, hphi, p4418_1]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [h4358, h4417, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4418_1, u4ehi0]
            · have p4418_0 := h4418c.1
              have p4418_1 := h4418c.2.1
              have p4418_2 := h4418c.2.2.1
              have p4418_3 := h4418c.2.2.2
              linarith only [hlam, p4418_0]
          · rcases h0bigk with h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [hlam, p4444_0]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h0, hlam, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h2352, hlam, p4444_0]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h2875, hlam, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h2994, hlam, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h0, hc01, hc12, hlam, hphi, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [hlam, p4444_0]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h3145, hlam, p4444_0]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h3689, hlam, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h3898, hlam, p4444_0]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h2352, h4416, hc01, hc12, hlam, hphi, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h3145, h4416, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [hlam, p4444_0]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h4022, hlam, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h4298, hlam, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h2875, h4417, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h0, h2875, h4417, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h2875, h4417, hc03, hc45, hlam, hphi, ht34, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [hlam, p4444_0]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h4358, hlam, p4444_0]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h2994, h4417, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h0, h2994, h4417, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h0, h2994, h3145, h4417, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4444_1]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [h2994, h4417, hc45, hlam, hphi, p4444_1, u4ehi0]
            · have p4444_0 := h4444c.1
              have p4444_1 := h4444c.2.1
              have p4444_2 := h4444c.2.2.1
              have p4444_3 := h4444c.2.2.2
              linarith only [hlam, p4444_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4470 | h4470
          · rcases h0bigk with h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c | h4471c
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [hlam, p4471_0]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h0, hlam, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h2352, hlam, p4471_0]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h2875, hlam, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h2994, hlam, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h0, hc01, hc12, hlam, hphi, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [hlam, p4471_0]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h3145, hlam, p4471_0]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h3689, hlam, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h3898, hlam, p4471_0]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h2352, h4416, hc01, hc23, hlam, hphi, ht12, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h2352, h4416, hc02, hc23, hlam, hphi, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [hlam, p4471_0]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h4022, hlam, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h4298, hlam, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h0, h3689, hc01, hc24, hlam, hphi, ht12, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h4022, hc03, hc34, hlam, hphi, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [hlam, p4471_0]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h4358, hlam, p4471_0]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h4358, h4470, hc01, hc14, hlam, hphi, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h0, h4358, h4470, hc01, hc14, hlam, hphi, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h0, h3145, h4358, h4470, hc01, hc14, hlam, hphi, p4471_1]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [h4358, h4470, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4471_1, u4ehi0]
            · have p4471_0 := h4471c.1
              have p4471_1 := h4471c.2.1
              have p4471_2 := h4471c.2.2.1
              have p4471_3 := h4471c.2.2.2
              linarith only [hlam, p4471_0]
          · rcases h0bigk with h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [hlam, p4497_0]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h0, hlam, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h2352, hlam, p4497_0]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h2875, hlam, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h2994, hlam, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h0, h4416, hc01, hc23, hlam, hphi, ht12, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [hlam, p4497_0]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h3145, hlam, p4497_0]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h3689, hlam, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h3898, hlam, p4497_0]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h2352, h4416, hc01, hc23, hlam, hphi, ht12, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h2352, h4416, hc02, hc23, hlam, hphi, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [hlam, p4497_0]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h4022, hlam, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h4298, hlam, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h2875, h4470, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h0, h2875, h4470, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h2875, h4470, hc03, hc45, hlam, hphi, ht34, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [hlam, p4497_0]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h4358, hlam, p4497_0]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h2994, h4470, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h0, h2994, h4470, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h0, h2994, h3145, h4470, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4497_1]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [h2994, h4470, hc45, hlam, hphi, p4497_1, u4ehi0]
            · have p4497_0 := h4497c.1
              have p4497_1 := h4497c.2.1
              have p4497_2 := h4497c.2.2.1
              have p4497_3 := h4497c.2.2.2
              linarith only [hlam, p4497_0]

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2875 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3145 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3689 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h3898 | h3898
  · exact r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x1_x1_x0 m hb0 hb4 h0 h2352 h2875 h2994 h3145 h3689 h3898
  · exact r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x1_x1_x1 m hb0 hb4 h0 h2352 h2875 h2994 h3145 h3689 h3898

end R2N4
