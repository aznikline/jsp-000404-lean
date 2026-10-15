import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_53S14
import Jsp000404.R1LeavesN7_53S15
import Jsp000404.R1LeavesN7_53S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1178 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1482 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1725 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1764 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h2110 | h2110
  · rcases m.htr 1 2 5 (by decide) (by decide) with h2111 | h2111
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2112 | h2112
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2113 | h2113
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2114 | h2114
          · rcases h1bigk with h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h0, hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h1178, hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h1482, hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h1725, hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2115_1]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h1764, hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h1764, h2114, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2115_1, u5ehi4]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h1764, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2115_1, u5ehi1]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h1764, hc01, hc23, hlam, hphi, ht12, p2115_1]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h1764, hc12, hc23, hlam, hphi, p2115_1]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h1764, h2114, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2115_1, u5ehi4]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h1725, h1764, hc01, hc23, hlam, hphi, ht12, p2115_1]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h2110, hc01, hc12, hlam, hphi, p2115_1]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h2110, hlam, p2115_1]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h2112, hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h1725, h1764, h2110, hc01, hc23, hlam, hphi, ht12, p2115_1]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2115_1]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h2111, hlam, p2115_1]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h2113, hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [h2114, hlam, p2115_0]
            · have p2115_0 := h2115c.1
              have p2115_1 := h2115c.2.1
              have p2115_2 := h2115c.2.2.1
              have p2115_3 := h2115c.2.2.2
              linarith only [hlam, p2115_0]
          · rcases h1bigk with h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [hlam, p2141_0]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h0, hlam, p2141_0]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1178, hlam, p2141_0]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1482, hlam, p2141_0]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1725, hlam, p2141_0]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1764, hc01, hc23, hlam, hphi, ht12, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [hlam, p2141_0]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1764, hlam, p2141_0]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1764, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1764, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2141_1, u5ehi1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1764, hc01, hc23, hlam, hphi, ht12, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1764, hc12, hc23, hlam, hphi, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [hlam, p2141_0]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1482, h1764, hc01, hc23, hlam, hphi, ht12, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1725, h1764, hc01, hc23, hlam, hphi, ht12, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h2110, hlam, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h2112, hlam, p2141_0]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [hlam, p2141_0]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h2114, hlam, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h2111, hlam, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h2113, hlam, p2141_0]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [h1764, h2111, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2141_1]
            · have p2141_0 := h2141c.1
              have p2141_1 := h2141c.2.1
              have p2141_2 := h2141c.2.2.1
              have p2141_3 := h2141c.2.2.2
              linarith only [hlam, p2141_0]
        · linarith only [h1764, h2111, h2113, hlam]
      · linarith only [h1764, h2110, h2112, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2169 | h2169
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2170 | h2170
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2171 | h2171
          · linarith only [h2110, h2111, h2171, hlam]
          · rcases h1bigk with h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h0, hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h1178, hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h1482, hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h1725, hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2173_1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h1764, hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h2111, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2173_1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h2111, hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h1764, hc01, hc23, hlam, hphi, ht12, p2173_1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h1764, hc12, hc23, hlam, hphi, p2173_1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h1482, h1764, hc01, hc23, hlam, hphi, ht12, p2173_1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h1764, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2173_1, u5ehi1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h2110, hc01, hc12, hlam, hphi, p2173_1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h2110, hlam, p2173_1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h2169, hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h2171, hlam, p2173_1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2173_1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h2111, hc12, hc25, hlam, hphi, p2173_1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h2170, hlam, p2173_0]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [h1482, h2171, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2173_1]
            · have p2173_0 := h2173c.1
              have p2173_1 := h2173c.2.1
              have p2173_2 := h2173c.2.2.1
              have p2173_3 := h2173c.2.2.2
              linarith only [hlam, p2173_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2199 | h2199
          · linarith only [h2110, h2111, h2199, hlam]
          · rcases h1bigk with h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [hlam, p2201_0]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h0, hlam, p2201_0]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h1178, hlam, p2201_0]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h1482, hlam, p2201_0]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h1725, hlam, p2201_0]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [hlam, p2201_0]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h1764, hlam, p2201_0]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h1764, h2170, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h2111, hlam, p2201_0]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h2170, hc01, hc35, hlam, hphi, ht12, ht23, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h2170, hc12, hc35, hlam, hphi, ht23, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [hlam, p2201_0]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h1482, h2170, hc01, hc35, hlam, hphi, ht12, ht23, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h2170, hlam, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h2110, hc01, hc12, hlam, hphi, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h2110, hlam, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h2169, hlam, p2201_0]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [hlam, p2201_0]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h2199, hlam, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h2111, hc12, hc25, hlam, hphi, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h2170, hc13, hc35, hlam, hphi, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [h1482, h2199, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2201_1]
            · have p2201_0 := h2201c.1
              have p2201_1 := h2201c.2.1
              have p2201_2 := h2201c.2.2.1
              have p2201_3 := h2201c.2.2.2
              linarith only [hlam, p2201_0]
      · linarith only [h1764, h2110, h2169, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h2228 | h2228
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2229 | h2229
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2230 | h2230
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2231 | h2231
          · rcases h1bigk with h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h0, hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h1178, hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h1482, hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h1725, hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2232_1]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h1764, hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h2110, hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h2110, h2229, hc13, hlam, hphi, ht01, ht0b, ht5b, p2232_1, u5ehi1]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p2232_1]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h1764, hc12, hc23, hlam, hphi, p2232_1]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h1764, h2231, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2232_1, u5ehi4]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h1725, h1764, hc01, hc23, hlam, hphi, ht12, p2232_1]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2232_1]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h2110, h2228, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p2232_1, u5ehi2]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h2229, hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h1725, h1764, h2229, hc01, hc23, hlam, hphi, ht12, p2232_1]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2232_1]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h2228, hlam, p2232_1]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h2230, hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [h2231, hlam, p2232_0]
            · have p2232_0 := h2232c.1
              have p2232_1 := h2232c.2.1
              have p2232_2 := h2232c.2.2.1
              have p2232_3 := h2232c.2.2.2
              linarith only [hlam, p2232_0]
          · linarith only [h2110, h2228, h2231, hlam]
        · linarith only [h1764, h2228, h2230, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2260 | h2260
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2261 | h2261
          · rcases h1bigk with h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h0, hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h1178, hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h1482, hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h1725, hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h1764, h2229, hc01, hc34, hlam, hphi, ht12, ht23, p2262_1]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h1764, hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h2110, hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h1764, h2229, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2262_1, u5ehi1]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h2229, hc01, hc34, hlam, hphi, ht12, ht23, p2262_1]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h2229, hc12, hc34, hlam, hphi, ht23, p2262_1]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h2229, hlam, p2262_1]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h1725, h2229, hc01, hc34, hlam, hphi, ht12, ht23, p2262_1]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2262_1]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h2110, h2228, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p2262_1, u5ehi2]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h2229, hc13, hc34, hlam, hphi, p2262_1]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h1725, h2229, hc01, hc34, hlam, hphi, ht12, ht23, p2262_1]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2262_1]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h2228, hlam, p2262_1]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h2260, hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [h2261, hlam, p2262_0]
            · have p2262_0 := h2262c.1
              have p2262_1 := h2262c.2.1
              have p2262_2 := h2262c.2.2.1
              have p2262_3 := h2262c.2.2.2
              linarith only [hlam, p2262_0]
          · linarith only [h2110, h2228, h2261, hlam]
        · linarith only [h1764, h2228, h2260, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2290 | h2290
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2291 | h2291
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2292 | h2292
          · rcases h1bigk with h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h0, hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h1178, hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h1482, hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h1725, hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2293_1]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h1764, hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h2110, hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h2228, hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p2293_1]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h1764, hc12, hc23, hlam, hphi, p2293_1]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h1764, h2292, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2293_1, u5ehi1]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h0, h1764, h2228, hc01, hc23, hlam, hphi, ht12, p2293_1]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2293_1]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h0, h2110, hc01, hc24, hlam, hphi, ht12, p2293_1]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h2290, hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h0, h1764, h2228, h2290, hc01, hc23, hlam, hphi, ht12, p2293_1]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2293_1]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h0, h2228, hc01, hc25, hlam, hphi, ht12, p2293_1]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h2291, hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [h2292, hlam, p2293_0]
            · have p2293_0 := h2293c.1
              have p2293_1 := h2293c.2.1
              have p2293_2 := h2293c.2.2.1
              have p2293_3 := h2293c.2.2.2
              linarith only [hlam, p2293_0]
          · rcases h1bigk with h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h0, hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h1178, hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h1482, hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h1725, hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2319_1]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h1764, hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h2110, hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h2228, hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h1764, hc01, hc23, hlam, hphi, ht12, p2319_1]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h1764, hc12, hc23, hlam, hphi, p2319_1]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h1482, h1764, hc01, hc23, hlam, hphi, ht12, p2319_1]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h1764, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2319_1, u5ehi1]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2319_1]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h0, h2110, hc01, hc24, hlam, hphi, ht12, p2319_1]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h2290, hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h2292, hlam, p2319_1]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2319_1]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h0, h2228, hc01, hc25, hlam, hphi, ht12, p2319_1]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h2291, hlam, p2319_0]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [h2292, hc14, hc45, hlam, hphi, p2319_1]
            · have p2319_0 := h2319c.1
              have p2319_1 := h2319c.2.1
              have p2319_2 := h2319c.2.2.1
              have p2319_3 := h2319c.2.2.2
              linarith only [hlam, p2319_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2345 | h2345
          · linarith only [h2290, h2291, h2345, hlam]
          · rcases h1bigk with h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c | h2347c
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h0, hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h1178, hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h1482, hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h1725, hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h1764, hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h2110, hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h2228, hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h2291, hc01, hc35, hlam, hphi, ht12, ht23, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h2291, hc12, hc35, hlam, hphi, ht23, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h2291, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h2291, hlam, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h0, h2345, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h2290, hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [hlam, p2347_0]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h2345, hlam, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h0, h2228, hc01, hc25, hlam, hphi, ht12, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h2291, hc13, hc35, hlam, hphi, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [h0, h2110, h2345, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2347_1]
            · have p2347_0 := h2347c.1
              have p2347_1 := h2347c.2.1
              have p2347_2 := h2347c.2.2.1
              have p2347_3 := h2347c.2.2.2
              linarith only [hlam, p2347_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2373 | h2373
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2374 | h2374
          · rcases h1bigk with h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h0, hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h1178, hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h1482, hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h1725, hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2375_1]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h1764, hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h2110, hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h2228, hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h2290, hc01, hc34, hlam, hphi, ht12, ht23, p2375_1]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h2290, hc12, hc34, hlam, hphi, ht23, p2375_1]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h2290, hlam, p2375_1]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h2290, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2375_1, u5ehi1]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2375_1]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h0, h2110, hc01, hc24, hlam, hphi, ht12, p2375_1]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h2290, hc13, hc34, hlam, hphi, p2375_1]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h0, h2228, h2290, hc01, hc34, hlam, hphi, ht12, ht23, p2375_1]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2375_1]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h0, h2228, hc01, hc25, hlam, hphi, ht12, p2375_1]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h2373, hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [h2374, hlam, p2375_0]
            · have p2375_0 := h2375c.1
              have p2375_1 := h2375c.2.1
              have p2375_2 := h2375c.2.2.1
              have p2375_3 := h2375c.2.2.2
              linarith only [hlam, p2375_0]
          · linarith only [h2290, h2373, h2374, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2402 | h2402
          · rcases h1bigk with h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h0, hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h1178, hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h1482, hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h1725, hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2403_1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h1764, hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h2110, hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h2228, hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p2403_1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h2373, hc12, hc35, hlam, hphi, ht23, p2403_1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h2290, hlam, p2403_1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h2373, hlam, p2403_1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2403_1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h0, h2110, hc01, hc24, hlam, hphi, ht12, p2403_1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h2290, hc13, hc34, hlam, hphi, p2403_1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h2290, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2403_1, u5ehi1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2403_1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h0, h2228, hc01, hc25, hlam, hphi, ht12, p2403_1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h0, h1764, h2373, hc01, hc35, hlam, hphi, ht12, ht23, p2403_1]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [h2402, hlam, p2403_0]
            · have p2403_0 := h2403c.1
              have p2403_1 := h2403c.2.1
              have p2403_2 := h2403c.2.2.1
              have p2403_3 := h2403c.2.2.2
              linarith only [hlam, p2403_0]
          · rcases h1bigk with h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h0, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1178, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1482, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1725, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1764, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h2110, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h2228, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h0, hc01, hc13, hlam, hphi, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h2290, hlam, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h2373, hlam, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h2402, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h0, h2402, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h2402, hc13, hc45, hlam, hphi, ht34, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h2402, hlam, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h2402, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h0, h2402, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h0, h1764, h2402, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h2402, hc14, hc45, hlam, hphi, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [hlam, p2429_0]

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1178 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1482 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1725 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1764 | h1764
  · exact r1l7_21_15_H_I_L_R_x1_x1_x1_x1_x0 m hb1 hb5 h0 h1178 h1482 h1725 h1764
  · exact r1l7_21_15_H_I_L_R_x1_x1_x1_x1_x1 m hb1 hb5 h0 h1178 h1482 h1725 h1764

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1178 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1482 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1725 | h1725
  · exact r1l7_21_15_H_I_L_R_x1_x1_x1_x0 m hb1 hb5 h0 h1178 h1482 h1725
  · exact r1l7_21_15_H_I_L_R_x1_x1_x1_x1 m hb1 hb5 h0 h1178 h1482 h1725

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1178 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1482 | h1482
  · exact r1l7_21_15_H_I_L_R_x1_x1_x0 m hb1 hb5 h0 h1178 h1482
  · exact r1l7_21_15_H_I_L_R_x1_x1_x1 m hb1 hb5 h0 h1178 h1482

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1178 | h1178
  · exact r1l7_21_15_H_I_L_R_x1_x0 m hb1 hb5 h0 h1178
  · exact r1l7_21_15_H_I_L_R_x1_x1 m hb1 hb5 h0 h1178

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_15_H_I_L_R_x0 m hb1 hb5 h0
  · exact r1l7_21_15_H_I_L_R_x1 m hb1 hb5 h0

end R2N4
