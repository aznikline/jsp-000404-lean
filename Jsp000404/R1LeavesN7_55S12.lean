import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_55S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h374 | h374
  · rcases m.htr 1 2 5 (by decide) (by decide) with h375 | h375
    · rcases m.htr 1 3 4 (by decide) (by decide) with h376 | h376
      · rcases m.htr 1 3 5 (by decide) (by decide) with h377 | h377
        · rcases m.htr 1 4 5 (by decide) (by decide) with h378 | h378
          · rcases h1bigk with h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h374, h378, hc01, hlam, hphi, ht0b, ht45, ht5b, p379_1, u4ehi4]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h374, h378, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p379_1, u4ehi4]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h378, hc01, hlam, hphi, ht0b, ht45, ht5b, p379_1, u4ehi4]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h378, hc01, hlam, hphi, ht0b, ht45, ht5b, p379_1, u4ehi4]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h0, hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h4, hlam, p379_1]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h378, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p379_1, u4ehi4]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p379_1]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h1, hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p379_1]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h1, h378, hc01, hlam, hphi, ht0b, ht45, ht5b, p379_1, u4ehi4]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h1, h375, hc01, hc25, hlam, hphi, ht0b, ht5b, p379_1]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h2, hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h374, hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h376, hlam, p379_1]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h0, h374, h375, hc01, hc25, hlam, hphi, ht0b, ht5b, p379_1]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h3, hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h375, hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h377, hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [h378, hlam, p379_0]
            · have p379_0 := h379c.1
              have p379_1 := h379c.2.1
              have p379_2 := h379c.2.2.1
              have p379_3 := h379c.2.2.2
              linarith only [hlam, p379_0]
          · rcases h1bigk with h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [hlam, p405_0]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h374, hc01, hlam, hphi, ht0b, ht45, ht5b, p405_1, u4ehi2]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h374, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p405_1, u4ehi2]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h374, hc01, hlam, hphi, ht0b, ht45, ht5b, p405_1, u4ehi2]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h374, h378, hc01, hlam, hphi, ht0b, ht45, ht5b, p405_1, u4ehi2]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h0, hlam, p405_0]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [hlam, p405_0]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h4, hlam, p405_1]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h374, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p405_1, u4ehi2]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h374, h378, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p405_1, u4ehi2]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h1, hlam, p405_0]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p405_1]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [hlam, p405_0]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h1, h374, hc01, hlam, hphi, ht0b, ht45, ht5b, p405_1, u4ehi2]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h1, h374, h378, hc01, hlam, hphi, ht0b, ht45, ht5b, p405_1, u4ehi2]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h2, hlam, p405_0]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h374, hlam, p405_0]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h376, hlam, p405_1]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [hlam, p405_0]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h378, hlam, p405_1]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h3, hlam, p405_0]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h375, hlam, p405_0]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h377, hlam, p405_0]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [h374, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p405_1, u4ehi2]
            · have p405_0 := h405c.1
              have p405_1 := h405c.2.1
              have p405_2 := h405c.2.2.1
              have p405_3 := h405c.2.2.2
              linarith only [hlam, p405_0]
        · linarith only [h375, h377, h4, hlam]
      · linarith only [h374, h376, h4, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
      · rcases m.htr 1 3 5 (by decide) (by decide) with h434 | h434
        · rcases m.htr 1 4 5 (by decide) (by decide) with h435 | h435
          · linarith only [h374, h375, h435, hlam]
          · rcases h1bigk with h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [hlam, p437_0]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h374, hc01, hlam, hphi, ht0b, ht45, ht5b, p437_1, u4ehi1]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h374, h375, h434, hc01, hlam, hphi, ht0b, ht45, ht5b, p437_1, u4ehi2]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p437_1, u4ehi1]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h374, h375, hc01, hlam, hphi, ht0b, ht45, ht5b, p437_1, u4ehi2]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h0, hlam, p437_0]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [hlam, p437_0]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h4, hlam, p437_1]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p437_1, u4ehi1]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h375, hlam, p437_1]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h1, hlam, p437_0]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p437_1]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [hlam, p437_0]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h1, h374, hc01, hlam, hphi, ht0b, ht45, ht5b, p437_1, u4ehi2]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p437_1]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h2, hlam, p437_0]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h374, hlam, p437_0]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h433, hlam, p437_1]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [hlam, p437_0]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h435, hlam, p437_1]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h3, hlam, p437_0]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h374, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p437_1, u4ehi2]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h434, hlam, p437_0]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [h1, h374, h434, hc01, hlam, hphi, ht0b, ht45, ht5b, p437_1, u4ehi2]
            · have p437_0 := h437c.1
              have p437_1 := h437c.2.1
              have p437_2 := h437c.2.2.1
              have p437_3 := h437c.2.2.2
              linarith only [hlam, p437_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h463 | h463
          · linarith only [h374, h375, h463, hlam]
          · rcases h1bigk with h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [hlam, p465_0]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h374, hc01, hlam, hphi, ht0b, ht45, ht5b, p465_1, u4ehi1]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h433, hc01, hlam, hphi, ht0b, ht45, ht5b, p465_1, u4ehi3]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p465_1, u4ehi1]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h433, h434, hc01, hlam, hphi, ht0b, ht45, ht5b, p465_1, u4ehi3]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h0, hlam, p465_0]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [hlam, p465_0]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h4, hlam, p465_1]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p465_1, u4ehi1]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h375, hlam, p465_1]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h1, hlam, p465_0]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h434, hc12, hc35, hlam, hphi, ht23, p465_1]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [hlam, p465_0]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h374, h434, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p465_1, u4ehi2]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h434, hlam, p465_1]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h2, hlam, p465_0]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h374, hlam, p465_0]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h433, hlam, p465_1]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [hlam, p465_0]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h463, hlam, p465_1]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h3, hlam, p465_0]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h374, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p465_1, u4ehi2]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p465_1]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [h3, h374, hc01, hlam, hphi, ht0b, ht45, ht5b, p465_1, u4ehi2]
            · have p465_0 := h465c.1
              have p465_1 := h465c.2.1
              have p465_2 := h465c.2.2.1
              have p465_3 := h465c.2.2.2
              linarith only [hlam, p465_0]
      · linarith only [h374, h4, h433, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
    · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
      · rcases m.htr 1 3 5 (by decide) (by decide) with h494 | h494
        · rcases m.htr 1 4 5 (by decide) (by decide) with h495 | h495
          · rcases h1bigk with h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [hlam, p496_0]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h492, hc01, hc25, hlam, hphi, ht0b, ht5b, p496_1]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h493, hc01, hlam, hphi, ht0b, ht45, ht5b, p496_1, u4ehi3]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h495, hc01, hlam, hphi, ht0b, ht45, ht5b, p496_1, u4ehi4]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h495, hc01, hlam, hphi, ht0b, ht45, ht5b, p496_1, u4ehi4]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h0, hlam, p496_0]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [hlam, p496_0]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h4, hlam, p496_1]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h374, hlam, p496_1]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p496_1]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h1, hlam, p496_0]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p496_1]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [hlam, p496_0]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h1, h495, hc01, hlam, hphi, ht0b, ht45, ht5b, p496_1, u4ehi4]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h1, h494, hc01, hc35, hlam, hphi, ht0b, ht5b, p496_1]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h2, hlam, p496_0]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h492, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p496_1]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h493, hlam, p496_1]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [hlam, p496_0]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h1, h493, h494, hc01, hc35, hlam, hphi, ht0b, ht5b, p496_1]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h3, hlam, p496_0]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h492, hlam, p496_0]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h494, hlam, p496_0]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [h495, hlam, p496_0]
            · have p496_0 := h496c.1
              have p496_1 := h496c.2.1
              have p496_2 := h496c.2.2.1
              have p496_3 := h496c.2.2.2
              linarith only [hlam, p496_0]
          · linarith only [h374, h492, h495, hlam]
        · linarith only [h4, h492, h494, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h524 | h524
        · rcases m.htr 1 4 5 (by decide) (by decide) with h525 | h525
          · rcases h1bigk with h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h492, hc01, hc25, hlam, hphi, ht0b, ht5b, p526_1]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h524, hc01, hc35, hlam, hphi, ht0b, ht5b, p526_1]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h525, hc01, hlam, hphi, ht0b, ht45, ht5b, p526_1, u4ehi4]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h525, hc01, hlam, hphi, ht0b, ht45, ht5b, p526_1, u4ehi4]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h0, hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h4, hlam, p526_1]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h374, hlam, p526_1]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p526_1]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h1, hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p526_1]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h493, hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h1, h492, hc01, hc25, hlam, hphi, ht0b, ht5b, p526_1]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h2, hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h2, h492, hc01, hc25, hlam, hphi, ht0b, ht5b, p526_1]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p526_1]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h2, h492, hc01, hc25, hlam, hphi, ht0b, ht5b, p526_1]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h3, hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h492, hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h524, hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [h525, hlam, p526_0]
            · have p526_0 := h526c.1
              have p526_1 := h526c.2.1
              have p526_2 := h526c.2.2.1
              have p526_3 := h526c.2.2.2
              linarith only [hlam, p526_0]
          · linarith only [h374, h492, h525, hlam]
        · linarith only [h4, h492, h524, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h554 | h554
      · rcases m.htr 1 3 5 (by decide) (by decide) with h555 | h555
        · rcases m.htr 1 4 5 (by decide) (by decide) with h556 | h556
          · rcases h1bigk with h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [hlam, p557_0]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              rcases p557_3 (m.d 0 1) (by simp) with h559 | h559
              · rcases p557_3 (m.d 1 2) (by simp) with h560 | h560
                · linarith only [h560, hlam, p557_0]
                · rcases p557_3 (m.d 1 3) (by simp) with h562 | h562
                  · linarith only [h1, h562, hlam]
                  · linarith only [h4, h562, hlam]
              · linarith only [h559, hlam, p557_0]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h554, h556, hc01, hlam, hphi, ht0b, ht45, ht5b, p557_1, u4ehi4]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h556, hc01, hlam, hphi, ht0b, ht45, ht5b, p557_1, u4ehi4]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h556, hc01, hlam, hphi, ht0b, ht45, ht5b, p557_1, u4ehi4]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h0, hlam, p557_0]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [hlam, p557_0]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h4, hlam, p557_1]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h374, hlam, p557_1]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h492, hlam, p557_1]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h1, hlam, p557_0]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p557_1]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [hlam, p557_0]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h1, h556, hc01, hlam, hphi, ht0b, ht45, ht5b, p557_1, u4ehi4]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h1, h556, hc01, hlam, hphi, ht0b, ht45, ht5b, p557_1, u4ehi4]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h2, hlam, p557_0]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p557_1]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h554, hlam, p557_1]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [hlam, p557_0]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h1, h554, h556, hc01, hlam, hphi, ht0b, ht45, ht5b, p557_1, u4ehi4]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h3, hlam, p557_0]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p557_1]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h555, hlam, p557_0]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [h556, hlam, p557_0]
            · have p557_0 := h557c.1
              have p557_1 := h557c.2.1
              have p557_2 := h557c.2.2.1
              have p557_3 := h557c.2.2.2
              linarith only [hlam, p557_0]
          · rcases h1bigk with h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              rcases p589_3 (m.d 0 1) (by simp) with h591 | h591
              · rcases p589_3 (m.d 1 2) (by simp) with h592 | h592
                · linarith only [h592, hlam, p589_0]
                · rcases p589_3 (m.d 1 3) (by simp) with h594 | h594
                  · linarith only [h1, h594, hlam]
                  · linarith only [h4, h594, hlam]
              · linarith only [h591, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h555, hc01, hc35, hlam, hphi, ht0b, ht5b, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p589_1, u4ehi1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h554, h556, hc01, hlam, hphi, ht0b, ht45, ht5b, p589_1, u4ehi3]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h0, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h4, hlam, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h374, hlam, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h492, hlam, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h1, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h1, h554, hc01, hlam, hphi, ht0b, ht45, ht5b, p589_1, u4ehi3]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h2, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h554, hlam, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h556, hlam, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h3, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h555, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h1, h555, hc01, hlam, hphi, ht0b, ht45, ht5b, p589_1, u4ehi1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [hlam, p589_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h621 | h621
          · linarith only [h554, h555, h621, hlam]
          · rcases h1bigk with h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [hlam, p623_0]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              rcases p623_3 (m.d 0 1) (by simp) with h625 | h625
              · rcases p623_3 (m.d 1 2) (by simp) with h626 | h626
                · linarith only [h626, hlam, p623_0]
                · rcases p623_3 (m.d 1 3) (by simp) with h628 | h628
                  · linarith only [h1, h628, hlam]
                  · linarith only [h4, h628, hlam]
              · linarith only [h625, hlam, p623_0]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h554, hc01, hlam, hphi, ht0b, ht45, ht5b, p623_1, u4ehi1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p623_1, u4ehi1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h554, h555, hc01, hlam, hphi, ht0b, ht45, ht5b, p623_1, u4ehi1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h0, hlam, p623_0]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [hlam, p623_0]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h4, hlam, p623_1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h374, hlam, p623_1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h492, hlam, p623_1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h1, hlam, p623_0]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h492, h555, hc12, hc25, hlam, hphi, p623_1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [hlam, p623_0]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h555, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p623_1, u4ehi1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h555, hlam, p623_1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h2, hlam, p623_0]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h621, hc12, hc45, hlam, hphi, ht23, ht34, p623_1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h554, hlam, p623_1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [hlam, p623_0]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h621, hlam, p623_1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h3, hlam, p623_0]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p623_1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p623_1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p623_1, u4ehi1]
            · have p623_0 := h623c.1
              have p623_1 := h623c.2.1
              have p623_2 := h623c.2.2.1
              have p623_3 := h623c.2.2.2
              linarith only [hlam, p623_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h655 | h655
        · rcases m.htr 1 4 5 (by decide) (by decide) with h656 | h656
          · rcases h1bigk with h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              rcases p657_3 (m.d 0 1) (by simp) with h659 | h659
              · rcases p657_3 (m.d 1 2) (by simp) with h660 | h660
                · linarith only [h660, hlam, p657_0]
                · rcases p657_3 (m.d 1 3) (by simp) with h662 | h662
                  · linarith only [h1, h662, hlam]
                  · linarith only [h4, h662, hlam]
              · linarith only [h659, hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h655, hc01, hc35, hlam, hphi, ht0b, ht5b, p657_1]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h656, hc01, hlam, hphi, ht0b, ht45, ht5b, p657_1, u4ehi4]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h656, hc01, hlam, hphi, ht0b, ht45, ht5b, p657_1, u4ehi4]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h0, hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h4, hlam, p657_1]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h374, hlam, p657_1]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h492, hlam, p657_1]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h1, hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p657_1]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h554, hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p657_1]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h2, hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p657_1]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p657_1]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h2, h492, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p657_1]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h3, hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p657_1]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h655, hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [h656, hlam, p657_0]
            · have p657_0 := h657c.1
              have p657_1 := h657c.2.1
              have p657_2 := h657c.2.2.1
              have p657_3 := h657c.2.2.2
              linarith only [hlam, p657_0]
          · linarith only [h554, h655, h656, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h690 | h690
          · rcases h1bigk with h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              rcases p691_3 (m.d 0 1) (by simp) with h693 | h693
              · rcases p691_3 (m.d 1 2) (by simp) with h694 | h694
                · linarith only [h694, hlam, p691_0]
                · rcases p691_3 (m.d 1 3) (by simp) with h696 | h696
                  · linarith only [h1, h696, hlam]
                  · linarith only [h4, h696, hlam]
              · linarith only [h693, hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              rcases p691_3 (m.d 0 1) (by simp) with h700 | h700
              · rcases p691_3 (m.d 1 2) (by simp) with h701 | h701
                · linarith only [h0, h701, hlam]
                · rcases p691_3 (m.d 1 3) (by simp) with h703 | h703
                  · linarith only [h703, hlam, p691_0]
                  · rcases p691_3 (m.d 1 4) (by simp) with h705 | h705
                    · linarith only [h2, h705, hlam]
                    · linarith only [h554, h705, hlam]
              · linarith only [h700, hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h690, hc01, hlam, hphi, ht0b, ht45, ht5b, p691_1, u4ehi4]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h690, hc01, hlam, hphi, ht0b, ht45, ht5b, p691_1, u4ehi4]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h0, hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h4, hlam, p691_1]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h374, hlam, p691_1]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h492, hlam, p691_1]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h1, hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h655, hc12, hc35, hlam, hphi, ht23, p691_1]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h554, hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h655, hlam, p691_1]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h2, hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p691_1]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p691_1]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h2, h690, hc01, hlam, hphi, ht0b, ht45, ht5b, p691_1, u4ehi4]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h3, hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p691_1]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h3, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p691_1]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [h690, hlam, p691_0]
            · have p691_0 := h691c.1
              have p691_1 := h691c.2.1
              have p691_2 := h691c.2.2.1
              have p691_3 := h691c.2.2.2
              linarith only [hlam, p691_0]
          · rcases h1bigk with h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [hlam, p731_0]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              rcases p731_3 (m.d 0 1) (by simp) with h733 | h733
              · rcases p731_3 (m.d 1 2) (by simp) with h734 | h734
                · linarith only [h734, hlam, p731_0]
                · rcases p731_3 (m.d 1 3) (by simp) with h736 | h736
                  · linarith only [h1, h736, hlam]
                  · linarith only [h4, h736, hlam]
              · linarith only [h733, hlam, p731_0]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              rcases p731_3 (m.d 0 1) (by simp) with h740 | h740
              · rcases p731_3 (m.d 1 2) (by simp) with h741 | h741
                · linarith only [h0, h741, hlam]
                · rcases p731_3 (m.d 1 3) (by simp) with h743 | h743
                  · linarith only [h743, hlam, p731_0]
                  · rcases p731_3 (m.d 1 4) (by simp) with h745 | h745
                    · linarith only [h2, h745, hlam]
                    · linarith only [h554, h745, hlam]
              · linarith only [h740, hlam, p731_0]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p731_1, u4ehi1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h690, hc01, hlam, hphi, ht0b, ht45, ht5b, p731_1, u4ehi1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h0, hlam, p731_0]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [hlam, p731_0]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h4, hlam, p731_1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h374, hlam, p731_1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h492, hlam, p731_1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h1, hlam, p731_0]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p731_1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [hlam, p731_0]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h554, hlam, p731_0]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h655, hlam, p731_1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h2, hlam, p731_0]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p731_1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p731_1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [hlam, p731_0]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h690, hlam, p731_1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h3, hlam, p731_0]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p731_1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h3, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p731_1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p731_1, u4ehi1]
            · have p731_0 := h731c.1
              have p731_1 := h731c.2.1
              have p731_2 := h731c.2.2.1
              have p731_3 := h731c.2.2.2
              linarith only [hlam, p731_0]

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_21_14_H_I_L_R_x0_x0_x0_x0_x0 m hb1 hb4 h0 h1 h2 h3 h4
  · exact r1l7_21_14_H_I_L_R_x0_x0_x0_x0_x1 m hb1 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h771 | h771
  · rcases m.htr 1 2 4 (by decide) (by decide) with h772 | h772
    · linarith only [h0, h3, h772, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h774 | h774
      · linarith only [h2, h3, h772, h774, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h776 | h776
        · linarith only [h1, h3, h774, h776, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h778 | h778
          · linarith only [h2, h3, h771, h772, h778, hlam]
          · linarith only [h2, h3, h771, h772, h778, hc23, hc35, hlam, hphi]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h781 | h781
    · linarith only [h0, h3, h781, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h783 | h783
      · linarith only [h1, h3, h771, h783, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h785 | h785
        · linarith only [h1, h3, h783, h785, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h787 | h787
          · linarith only [h2, h3, h785, h787, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h789 | h789
            · linarith only [h2, h3, h787, h789, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
            · linarith only [h2, h3, h789, hc45, hlam, hphi, u4ehi1]

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_21_14_H_I_L_R_x0_x0_x0_x0 m hb1 hb4 h0 h1 h2 h3
  · exact r1l7_21_14_H_I_L_R_x0_x0_x0_x1 m hb1 hb4 h0 h1 h2 h3

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h792 | h792
  · rcases m.htr 1 2 3 (by decide) (by decide) with h793 | h793
    · rcases m.htr 1 2 4 (by decide) (by decide) with h794 | h794
      · linarith only [h0, h2, h794, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h796 | h796
        · rcases m.htr 1 3 4 (by decide) (by decide) with h797 | h797
          · linarith only [h1, h2, h794, h797, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · linarith only [h0, h2, h793, h797, hc23, hc34, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h800 | h800
          · linarith only [h2, h792, h793, h794, h796, h800, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · linarith only [h2, h792, h793, h796, h800, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h803 | h803
      · linarith only [h0, h2, h803, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h805 | h805
        · rcases m.htr 1 3 4 (by decide) (by decide) with h806 | h806
          · linarith only [h1, h2, h803, h806, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h808 | h808
            · rcases m.htr 1 4 5 (by decide) (by decide) with h809 | h809
              · rcases h1bigk with h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h2, h806, hc12, hc34, hlam, hphi, ht23, p810_1]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h2, h806, hc13, hc34, hlam, hphi, p810_1]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h2, hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h2, h806, h809, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p810_1, u4ehi4]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h0, hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h793, hlam, p810_1]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h803, hlam, p810_1]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h809, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1, u4ehi4]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h1, hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h1, h2, h806, hc12, hc34, hlam, hphi, ht23, p810_1]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h806, hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h1, h2, h806, h809, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p810_1, u4ehi4]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h806, hc01, hc34, hlam, hphi, ht12, ht23, p810_1]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h805, h806, h809, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p810_1, u4ehi4]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h793, h805, h806, h809, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p810_1, u4ehi4]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h806, h809, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p810_1, u4ehi4]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h792, hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h805, hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h808, hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [h809, hlam, p810_0]
                · have p810_0 := h810c.1
                  have p810_1 := h810c.2.1
                  have p810_2 := h810c.2.2.1
                  have p810_3 := h810c.2.2.2
                  linarith only [hlam, p810_0]
              · linarith only [h1, h2, h793, h809, hc12, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h793, h805, h808, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h838 | h838
          · linarith only [h1, h2, h838, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h840 | h840
            · rcases m.htr 1 4 5 (by decide) (by decide) with h841 | h841
              · rcases h1bigk with h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [hlam, p842_0]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h2, h838, hc12, hc34, hlam, hphi, ht23, p842_1]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h2, h838, hc13, hc34, hlam, hphi, p842_1]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h2, hlam, p842_0]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h2, h838, h841, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p842_1, u4ehi4]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h0, hlam, p842_0]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [hlam, p842_0]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h793, hlam, p842_1]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h803, hlam, p842_1]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h805, hlam, p842_1]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h1, hlam, p842_0]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h1, h2, h838, hc12, hc34, hlam, hphi, ht23, p842_1]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [hlam, p842_0]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h838, hlam, p842_0]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h1, h2, h838, h841, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p842_1, u4ehi4]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h838, hc01, hc34, hlam, hphi, ht12, ht23, p842_1]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h838, hc12, hc34, hlam, hphi, ht23, p842_1]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h793, h838, hc12, hc34, hlam, hphi, ht23, p842_1]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [hlam, p842_0]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h838, h841, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p842_1, u4ehi4]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h792, hlam, p842_0]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h1, h840, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p842_1]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h840, hlam, p842_0]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [h841, hlam, p842_0]
                · have p842_0 := h842c.1
                  have p842_1 := h842c.2.1
                  have p842_2 := h842c.2.2.1
                  have p842_3 := h842c.2.2.2
                  linarith only [hlam, p842_0]
              · linarith only [h1, h2, h841, hc13, hc45, hlam, hphi, ht34]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h869 | h869
              · rcases h1bigk with h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h2, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h2, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h2, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h793, hlam, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h803, hlam, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h805, hlam, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h1, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h840, hc12, hc35, hlam, hphi, ht23, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h838, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h840, hlam, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hc01, hc14, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h803, hc12, hc24, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h793, h838, hc12, hc34, hlam, hphi, ht23, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h793, h838, h840, hc12, hc34, hlam, hphi, ht23, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h792, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h792, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h2, h792, h793, h838, hc12, hc34, hlam, hphi, ht23, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h869, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
              · linarith only [h0, h2, h869, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h897 | h897
    · rcases m.htr 1 2 4 (by decide) (by decide) with h898 | h898
      · linarith only [h0, h2, h898, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h900 | h900
        · linarith only [h0, h792, h900, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h902 | h902
          · linarith only [h0, h2, h897, h898, h902, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · linarith only [h0, h2, h897, h902, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h905 | h905
      · linarith only [h1, h2, h897, h905, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h907 | h907
        · linarith only [h1, h792, h897, h907, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h909 | h909
          · linarith only [h1, h2, h905, h909, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h911 | h911
            · linarith only [h1, h792, h911, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h913 | h913
              · rcases h1bigk with h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [hlam, p914_0]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h792, h909, h913, hc12, hc34, hlam, hphi, ht23, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h792, h909, h913, hc13, hc34, hlam, hphi, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h2, hlam, p914_0]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h792, hlam, p914_0]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h0, hlam, p914_0]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [hlam, p914_0]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h897, hlam, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h905, hlam, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h907, hlam, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h1, hlam, p914_0]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h1, h792, h909, h913, hc12, hc34, hlam, hphi, ht23, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [hlam, p914_0]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h909, hlam, p914_0]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h911, hlam, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h909, hc01, hc34, hlam, hphi, ht12, ht23, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h909, hc12, hc34, hlam, hphi, ht23, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h897, h909, hc12, hc34, hlam, hphi, ht23, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [hlam, p914_0]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h1, h792, h897, h909, hc12, hc34, hlam, hphi, ht23, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h1, h897, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h911, hc12, hc35, hlam, hphi, ht23, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h897, h911, hc12, hc35, hlam, hphi, ht23, p914_1]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [h913, hlam, p914_0]
                · have p914_0 := h914c.1
                  have p914_1 := h914c.2.1
                  have p914_2 := h914c.2.2.1
                  have p914_3 := h914c.2.2.2
                  linarith only [hlam, p914_0]
              · linarith only [h1, h2, h897, h913, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
