import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1108 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1352 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1405 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1478 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h1479 | h1479
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1480 | h1480
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1481 | h1481
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1482 | h1482
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1483 | h1483
          · rcases h1bigk with h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c | h1484c
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h0, hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1108, hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1352, hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1405, hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1484_1]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1481, h1483, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1484_1, u4ehi4]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1483, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1484_1, u4ehi4]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1405, hc01, hc12, hlam, hphi, p1484_1]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1484_1]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1478, hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1478, h1483, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1484_1, u4ehi4]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1405, h1478, hc01, hc12, hlam, hphi, p1484_1]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1484_1]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1479, hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1481, hlam, p1484_1]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1405, h1478, h1481, hc01, hc12, hlam, hphi, p1484_1]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1484_1]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1480, hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1482, hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [h1483, hlam, p1484_0]
            · have p1484_0 := h1484c.1
              have p1484_1 := h1484c.2.1
              have p1484_2 := h1484c.2.2.1
              have p1484_3 := h1484c.2.2.2
              linarith only [hlam, p1484_0]
          · rcases h1bigk with h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h0, hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1108, hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1352, hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1405, hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1510_1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1482, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1510_1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1510_1, u4ehi1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1405, hc01, hc12, hlam, hphi, p1510_1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1510_1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1478, hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1352, h1478, hc01, hc12, hlam, hphi, p1510_1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1405, h1478, hc01, hc12, hlam, hphi, p1510_1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1510_1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1479, hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1481, hlam, p1510_1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1483, hlam, p1510_1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1510_1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1480, hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1482, hlam, p1510_0]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [h1483, hc45, hlam, hphi, p1510_1, u4ehi1]
            · have p1510_0 := h1510c.1
              have p1510_1 := h1510c.2.1
              have p1510_2 := h1510c.2.2.1
              have p1510_3 := h1510c.2.2.2
              linarith only [hlam, p1510_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1536 | h1536
          · linarith only [h1481, h1482, h1536, hlam]
          · rcases h1bigk with h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [hlam, p1538_0]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h0, hlam, p1538_0]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1108, hlam, p1538_0]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1352, hlam, p1538_0]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1405, hlam, p1538_0]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1538_1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [hlam, p1538_0]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1108, hc01, hc12, hlam, hphi, p1538_1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1538_1, u4ehi1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1108, h1482, hc01, hc12, hlam, hphi, p1538_1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1538_1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1478, hlam, p1538_0]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [hlam, p1538_0]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1352, h1480, h1482, hc01, hc12, hlam, hphi, p1538_1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1482, hlam, p1538_1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1538_1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1479, hlam, p1538_0]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1481, hlam, p1538_1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [hlam, p1538_0]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1536, hlam, p1538_1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1480, hc01, hc12, hlam, hphi, p1538_1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1480, hlam, p1538_0]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1108, h1480, hc01, hc12, hlam, hphi, p1538_1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [h1536, hc45, hlam, hphi, p1538_1, u4ehi1]
            · have p1538_0 := h1538c.1
              have p1538_1 := h1538c.2.1
              have p1538_2 := h1538c.2.2.1
              have p1538_3 := h1538c.2.2.2
              linarith only [hlam, p1538_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1564 | h1564
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1565 | h1565
          · rcases h1bigk with h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h0, hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1108, hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1352, hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1405, hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1566_1]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1564, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1566_1]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1565, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1566_1, u4ehi4]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1405, hc01, hc12, hlam, hphi, p1566_1]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1566_1]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1478, hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1481, hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1405, h1481, hc01, hc34, hlam, hphi, ht12, ht23, p1566_1]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1566_1]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1479, hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1481, hc13, hc34, hlam, hphi, p1566_1]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1405, h1481, hc01, hc34, hlam, hphi, ht12, ht23, p1566_1]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1564, hc01, hc13, hlam, hphi, p1566_1]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1480, hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1564, hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [h1565, hlam, p1566_0]
            · have p1566_0 := h1566c.1
              have p1566_1 := h1566c.2.1
              have p1566_2 := h1566c.2.2.1
              have p1566_3 := h1566c.2.2.2
              linarith only [hlam, p1566_0]
          · linarith only [h1481, h1564, h1565, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1593 | h1593
          · rcases h1bigk with h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h0, hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1108, hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1352, hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1405, hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1594_1]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1108, hc01, hc12, hlam, hphi, p1594_1]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1593, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1594_1, u4ehi4]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1108, h1564, hc01, hc12, hlam, hphi, p1594_1]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1594_1]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1478, hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1481, hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1564, hlam, p1594_1]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1594_1]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1479, hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1481, hc13, hc34, hlam, hphi, p1594_1]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1405, h1481, hc01, hc34, hlam, hphi, ht12, ht23, p1594_1]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1594_1]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1480, hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1108, h1564, hc01, hc35, hlam, hphi, ht12, ht23, p1594_1]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [h1593, hlam, p1594_0]
            · have p1594_0 := h1594c.1
              have p1594_1 := h1594c.2.1
              have p1594_2 := h1594c.2.2.1
              have p1594_3 := h1594c.2.2.2
              linarith only [hlam, p1594_0]
          · rcases h1bigk with h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c | h1620c
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h0, hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1108, hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1352, hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1405, hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1620_1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1108, hc01, hc12, hlam, hphi, p1620_1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1620_1, u4ehi1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1405, hc01, hc12, hlam, hphi, p1620_1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1620_1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1478, hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1481, hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1564, hlam, p1620_1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1620_1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1479, hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1481, hc13, hc34, hlam, hphi, p1620_1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1593, hlam, p1620_1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1620_1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1480, hlam, p1620_0]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1108, h1564, hc01, hc35, hlam, hphi, ht12, ht23, p1620_1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [h1593, hc45, hlam, hphi, p1620_1, u4ehi1]
            · have p1620_0 := h1620c.1
              have p1620_1 := h1620c.2.1
              have p1620_2 := h1620c.2.2.1
              have p1620_3 := h1620c.2.2.2
              linarith only [hlam, p1620_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1646 | h1646
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1647 | h1647
        · linarith only [h1478, h1480, h1647, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1649 | h1649
          · linarith only [h1478, h1480, h1646, h1649, hlam]
          · rcases h1bigk with h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c | h1651c
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [hlam, p1651_0]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h0, hlam, p1651_0]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1108, hlam, p1651_0]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1352, hlam, p1651_0]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1405, hlam, p1651_0]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [hlam, p1651_0]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1108, h1480, hc01, hc15, hlam, hphi, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1480, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p1651_1, u4ehi1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1480, hlam, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1478, hlam, p1651_0]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [hlam, p1651_0]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1352, h1647, hc01, hc35, hlam, hphi, ht12, ht23, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1647, hlam, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1479, hlam, p1651_0]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1646, hlam, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [hlam, p1651_0]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1649, hlam, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1480, hc01, hc25, hlam, hphi, ht12, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1480, hc12, hc25, hlam, hphi, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1646, h1647, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1651_1, u4ehi3]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [h1352, h1649, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1651_1]
            · have p1651_0 := h1651c.1
              have p1651_1 := h1651c.2.1
              have p1651_2 := h1651c.2.2.1
              have p1651_3 := h1651c.2.2.2
              linarith only [hlam, p1651_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1677 | h1677
        · linarith only [h1479, h1480, h1646, h1677, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1679 | h1679
          · linarith only [h1479, h1480, h1679, hlam]
          · rcases h1bigk with h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c | h1681c
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [hlam, p1681_0]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h0, hlam, p1681_0]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1108, hlam, p1681_0]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1352, hlam, p1681_0]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1405, hlam, p1681_0]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1480, hc01, hc25, hlam, hphi, ht12, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [hlam, p1681_0]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1480, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1480, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1681_1, u4ehi1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1480, hlam, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1478, hlam, p1681_0]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [hlam, p1681_0]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1646, hlam, p1681_0]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1677, hlam, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1479, hlam, p1681_0]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1479, h1480, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [hlam, p1681_0]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1679, hlam, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1480, hc12, hc25, hlam, hphi, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1108, h1677, hc01, hc35, hlam, hphi, ht12, ht23, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [h1108, h1646, h1679, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1681_1]
            · have p1681_0 := h1681c.1
              have p1681_1 := h1681c.2.1
              have p1681_2 := h1681c.2.2.1
              have p1681_3 := h1681c.2.2.2
              linarith only [hlam, p1681_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1707 | h1707
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1708 | h1708
      · linarith only [h1478, h1479, h1708, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1710 | h1710
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1711 | h1711
          · rcases h1bigk with h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h0, hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1108, hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1352, hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1405, hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1479, hc01, hc24, hlam, hphi, ht12, p1712_1]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1479, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1712_1]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1479, hlam, p1712_1]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1405, h1479, hc01, hc24, hlam, hphi, ht12, p1712_1]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1712_1]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1478, hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1708, hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1405, h1708, hc01, hc34, hlam, hphi, ht12, ht23, p1712_1]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1712_1]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1479, hc12, hc24, hlam, hphi, p1712_1]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1708, hc13, hc34, hlam, hphi, p1712_1]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1405, h1708, hc01, hc34, hlam, hphi, ht12, ht23, p1712_1]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1478, h1710, hc01, hc12, hlam, hphi, p1712_1]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1707, hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1710, hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [h1711, hlam, p1712_0]
            · have p1712_0 := h1712c.1
              have p1712_1 := h1712c.2.1
              have p1712_2 := h1712c.2.2.1
              have p1712_3 := h1712c.2.2.2
              linarith only [hlam, p1712_0]
          · linarith only [h1478, h1479, h1710, h1711, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1739 | h1739
          · rcases h1bigk with h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h0, hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1108, hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1352, hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1405, hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1108, h1479, hc01, hc14, hlam, hphi, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1479, hlam, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1405, h1479, hc01, hc14, hlam, hphi, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1478, hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1708, hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1710, hlam, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h0, hc01, hc14, hlam, hphi, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1708, hc13, hc34, hlam, hphi, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1108, h1708, h1710, hc01, hc34, hlam, hphi, ht12, ht23, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1707, hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1108, h1479, h1707, hc01, hc24, hlam, hphi, ht12, p1740_1]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [h1739, hlam, p1740_0]
            · have p1740_0 := h1740c.1
              have p1740_1 := h1740c.2.1
              have p1740_2 := h1740c.2.2.1
              have p1740_3 := h1740c.2.2.2
              linarith only [hlam, p1740_0]
          · linarith only [h1479, h1707, h1739, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1767 | h1767
      · linarith only [h1478, h1479, h1767, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1769 | h1769
        · linarith only [h1478, h1707, h1769, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1771 | h1771
          · rcases h1bigk with h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [hlam, p1772_0]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h0, hlam, p1772_0]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1108, hlam, p1772_0]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1352, hlam, p1772_0]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1405, hlam, p1772_0]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [hlam, p1772_0]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1707, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1479, hlam, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1707, hlam, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1478, hlam, p1772_0]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [hlam, p1772_0]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1767, hlam, p1772_0]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1769, hlam, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1479, hc12, hc24, hlam, hphi, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1767, hc13, hc34, hlam, hphi, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [hlam, p1772_0]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1405, h1767, hc01, hc34, hlam, hphi, ht12, ht23, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1108, h1478, h1707, hc01, hc25, hlam, hphi, ht12, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1108, h1769, hc01, hc35, hlam, hphi, ht12, ht23, p1772_1]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [h1771, hlam, p1772_0]
            · have p1772_0 := h1772c.1
              have p1772_1 := h1772c.2.1
              have p1772_2 := h1772c.2.2.1
              have p1772_3 := h1772c.2.2.2
              linarith only [hlam, p1772_0]
          · rcases h1bigk with h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [hlam, p1798_0]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h0, hlam, p1798_0]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1108, hlam, p1798_0]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1352, hlam, p1798_0]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1405, hlam, p1798_0]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [hlam, p1798_0]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1108, hc01, hc12, hlam, hphi, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1479, hlam, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1707, hlam, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1478, hlam, p1798_0]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [hlam, p1798_0]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1767, hlam, p1798_0]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1769, hlam, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1771, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1771, hc12, hc45, hlam, hphi, ht23, ht34, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1108, h1771, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [hlam, p1798_0]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1771, hlam, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1771, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1108, h1478, h1771, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1108, h1771, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1798_1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [h1771, hc45, hlam, hphi, p1798_1, u4ehi1]
            · have p1798_0 := h1798c.1
              have p1798_1 := h1798c.2.1
              have p1798_2 := h1798c.2.2.1
              have p1798_3 := h1798c.2.2.2
              linarith only [hlam, p1798_0]

end R2N4
