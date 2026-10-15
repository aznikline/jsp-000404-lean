import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_49S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h353 | h353
  · rcases m.htr 0 2 5 (by decide) (by decide) with h354 | h354
    · rcases m.htr 0 3 4 (by decide) (by decide) with h355 | h355
      · rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
        · rcases m.htr 0 4 5 (by decide) (by decide) with h357 | h357
          · rcases m.htr 1 2 4 (by decide) (by decide) with h358 | h358
            · rcases m.htr 2 3 4 (by decide) (by decide) with h359 | h359
              · rcases h0bigk with h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h354, hc01, hc25, hlam, hphi, ht0b, ht5b, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h356, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u3ehi4]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h357, hc01, hc45, hlam, hphi, ht0b, ht5b, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h356, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u3ehi4]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h0, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h4, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h355, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u3ehi3]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h1, hlam, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h355, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p360_1, u3ehi3]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h356, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p360_1, u3ehi4]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h2, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h353, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h355, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h353, h356, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u3ehi4]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h3, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h354, hlam, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h356, hlam, p360_0]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [h357, hlam, p360_1]
                · have p360_0 := h360c.1
                  have p360_1 := h360c.2.1
                  have p360_2 := h360c.2.2.1
                  have p360_3 := h360c.2.2.2
                  linarith only [hlam, p360_0]
              · linarith only [h354, h356, h359, h4, hc34, hlam, hphi, u3ehi4]
            · linarith only [h353, h358, h4, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h388 | h388
            · rcases m.htr 2 3 4 (by decide) (by decide) with h389 | h389
              · rcases h0bigk with h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h353, h389, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p390_1, u3ehi3]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p390_1, u3ehi0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h2, h388, h389, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p390_1, u3ehi3]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h2, h357, h388, h389, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p390_1, u3ehi3]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h0, hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h4, hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h2, h388, h389, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p390_1, u3ehi3]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h2, h357, h388, h389, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p390_1, u3ehi3]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h1, hlam, p390_1]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p390_1]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h2, h388, h389, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p390_1, u3ehi3]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h2, h357, h388, h389, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p390_1, u3ehi3]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h2, hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h353, hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h355, hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h357, hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h3, hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h354, hlam, p390_1]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h356, hlam, p390_0]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [h2, h388, h389, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p390_1, u3ehi3]
                · have p390_0 := h390c.1
                  have p390_1 := h390c.2.1
                  have p390_2 := h390c.2.2.1
                  have p390_3 := h390c.2.2.2
                  linarith only [hlam, p390_0]
              · linarith only [h355, h389, h4, hlam]
            · linarith only [h353, h388, h4, hc12, hc23, hlam, hphi]
        · linarith only [h355, h356, hc35, hlam, hphi, u3ehi3]
      · linarith only [h353, h355, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h420 | h420
      · rcases m.htr 0 3 5 (by decide) (by decide) with h421 | h421
        · rcases m.htr 0 4 5 (by decide) (by decide) with h422 | h422
          · linarith only [h353, h354, h422, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h424 | h424
            · rcases m.htr 2 3 4 (by decide) (by decide) with h425 | h425
              · rcases h0bigk with h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, h424, h425, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1, u3ehi3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, h354, h421, h424, h425, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1, u3ehi3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h2, h424, h425, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1, u3ehi3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, h354, h424, h425, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1, u3ehi3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h4, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h2, h424, h425, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1, u3ehi3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h354, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h1, hlam, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h2, h4, h424, h425, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p426_1, u3ehi3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, h354, h4, h424, h425, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p426_1, u3ehi3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h2, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h353, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h420, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h422, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h3, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, h424, h425, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1, u3ehi3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h421, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h2, h422, h424, h425, hc45, hlam, hphi, ht34, p426_1, u3ehi3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
              · linarith only [h4, h421, h425, hc34, hlam, hphi, u3ehi4]
            · linarith only [h353, h4, h424, hc12, hc23, hlam, hphi]
        · linarith only [h420, h421, hc35, hlam, hphi, u3ehi3]
      · linarith only [h353, h4, h420, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h456 | h456
    · rcases m.htr 0 3 4 (by decide) (by decide) with h457 | h457
      · rcases m.htr 0 3 5 (by decide) (by decide) with h458 | h458
        · rcases m.htr 0 4 5 (by decide) (by decide) with h459 | h459
          · rcases m.htr 1 2 4 (by decide) (by decide) with h460 | h460
            · linarith only [h0, h353, h456, h460, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h462 | h462
              · rcases h0bigk with h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h456, h458, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p463_1, u3ehi4]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p463_1, u3ehi0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h459, hc01, hc45, hlam, hphi, ht0b, ht5b, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h458, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p463_1, u3ehi4]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h0, hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h4, hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h353, hlam, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h458, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p463_1, u3ehi4]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h1, hlam, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h353, h4, h456, h458, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p463_1, u3ehi4]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h4, h458, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p463_1, u3ehi4]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h2, hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h456, h458, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p463_1, u3ehi4]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h457, hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h4, h457, h458, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p463_1, u3ehi4]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h3, hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h456, hlam, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h458, hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h459, hlam, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hlam, p463_0]
              · linarith only [h4, h456, h458, h462, hc34, hlam, hphi, u3ehi4]
          · linarith only [h353, h456, h459, hlam]
        · linarith only [h457, h458, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h492 | h492
        · linarith only [h457, h492, hc34, hlam, hphi, u3ehi4]
        · linarith only [h4, h456, h492, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h495 | h495
      · rcases m.htr 0 3 5 (by decide) (by decide) with h496 | h496
        · rcases m.htr 0 4 5 (by decide) (by decide) with h497 | h497
          · rcases m.htr 1 2 4 (by decide) (by decide) with h498 | h498
            · linarith only [h0, h353, h498, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h500 | h500
              · rcases h0bigk with h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [hlam, p501_0]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  rcases p501_3 (m.d 0 1) (by simp) with h503 | h503
                  · rcases p501_3 (m.d 0 2) (by simp) with h504 | h504
                    · linarith only [h0, h504, hlam]
                    · rcases p501_3 (m.d 0 3) (by simp) with h506 | h506
                      · linarith only [h1, h506, hlam]
                      · linarith only [h4, h506, hlam]
                  · linarith only [h0, h503, hlam]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h495, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p501_1, u3ehi3]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h497, hc01, hc45, hlam, hphi, ht0b, ht5b, p501_1]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h496, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p501_1, u3ehi4]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h0, hlam, p501_0]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [hlam, p501_0]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h4, hlam, p501_0]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h353, hlam, p501_1]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h456, hlam, p501_0]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h1, hlam, p501_1]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p501_1]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [hlam, p501_0]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h4, h495, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p501_1, u3ehi3]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h4, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p501_1, u3ehi4]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h2, hlam, p501_0]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h0, h353, hc12, hc24, hlam, hphi, p501_1]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h495, hlam, p501_0]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [hlam, p501_0]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h4, h495, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p501_1, u3ehi4]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h3, hlam, p501_0]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h0, h456, hc12, hc25, hlam, hphi, p501_1]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h496, hlam, p501_0]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [h497, hlam, p501_1]
                · have p501_0 := h501c.1
                  have p501_1 := h501c.2.1
                  have p501_2 := h501c.2.2.1
                  have p501_3 := h501c.2.2.2
                  linarith only [hlam, p501_0]
              · linarith only [h4, h495, h500, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h534 | h534
            · linarith only [h0, h353, h534, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h536 | h536
              · rcases h0bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  rcases p537_3 (m.d 0 1) (by simp) with h539 | h539
                  · rcases p537_3 (m.d 0 2) (by simp) with h540 | h540
                    · linarith only [h0, h540, hlam]
                    · rcases p537_3 (m.d 0 3) (by simp) with h542 | h542
                      · linarith only [h1, h542, hlam]
                      · linarith only [h4, h542, hlam]
                  · linarith only [h0, h539, hlam]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h495, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p537_1, u3ehi3]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h495, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p537_1, u3ehi3]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h495, h497, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p537_1, u3ehi3]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h4, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h353, hlam, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h456, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h1, hlam, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, h353, h4, hc12, hc23, hlam, hphi, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h4, h495, h497, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p537_1, u3ehi3]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h2, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, h353, hc12, hc24, hlam, hphi, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h495, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h497, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h3, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, h456, hc12, hc25, hlam, hphi, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h496, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, h353, h456, hc12, hc25, hlam, hphi, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
              · linarith only [h4, h495, h536, hlam]
        · linarith only [h495, h496, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h571 | h571
        · linarith only [h495, h571, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h573 | h573
          · rcases m.htr 1 2 4 (by decide) (by decide) with h574 | h574
            · linarith only [h0, h353, h574, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h576 | h576
              · rcases h0bigk with h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [hlam, p577_0]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  rcases p577_3 (m.d 0 1) (by simp) with h579 | h579
                  · rcases p577_3 (m.d 0 2) (by simp) with h580 | h580
                    · linarith only [h0, h580, hlam]
                    · rcases p577_3 (m.d 0 3) (by simp) with h582 | h582
                      · linarith only [h1, h582, hlam]
                      · linarith only [h4, h582, hlam]
                  · linarith only [h0, h579, hlam]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1, u3ehi0]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h1, h571, h573, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1, u3ehi1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h1, h571, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1, u3ehi1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h0, hlam, p577_0]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [hlam, p577_0]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h4, hlam, p577_0]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h353, hlam, p577_1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h456, hlam, p577_0]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h1, hlam, p577_1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h0, h571, hc12, hc35, hlam, hphi, ht23, p577_1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [hlam, p577_0]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h495, hlam, p577_1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h571, hlam, p577_1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h2, hlam, p577_0]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h0, h353, hc12, hc24, hlam, hphi, p577_1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h1, h495, h576, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p577_1, u3ehi1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [hlam, p577_0]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h1, h495, h571, h576, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p577_1, u3ehi1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h3, hlam, p577_0]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h0, h456, hc12, hc25, hlam, hphi, p577_1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h1, h571, hc35, hlam, hphi, p577_1, u3ehi1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [h573, hlam, p577_1]
                · have p577_0 := h577c.1
                  have p577_1 := h577c.2.1
                  have p577_2 := h577c.2.2.1
                  have p577_3 := h577c.2.2.2
                  linarith only [hlam, p577_0]
              · rcases h0bigk with h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [hlam, p609_0]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  rcases p609_3 (m.d 0 1) (by simp) with h611 | h611
                  · rcases p609_3 (m.d 0 2) (by simp) with h612 | h612
                    · linarith only [h0, h612, hlam]
                    · rcases p609_3 (m.d 0 3) (by simp) with h614 | h614
                      · linarith only [h1, h614, hlam]
                      · linarith only [h4, h614, hlam]
                  · linarith only [h0, h611, hlam]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p609_1, u3ehi1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h573, hc01, hc45, hlam, hphi, ht0b, ht5b, p609_1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h1, h571, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p609_1, u3ehi1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h0, hlam, p609_0]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [hlam, p609_0]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h4, hlam, p609_0]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h353, hlam, p609_1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h456, hlam, p609_0]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h1, hlam, p609_1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p609_1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [hlam, p609_0]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h495, hlam, p609_1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h571, hlam, p609_1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h2, hlam, p609_0]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h0, h353, h576, hc12, hc34, hlam, hphi, ht23, p609_1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h353, h576, hc34, hlam, hphi, p609_1, u3ehi0]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [hlam, p609_0]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h1, h353, h571, h576, hc34, hlam, hphi, p609_1, u3ehi1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h3, hlam, p609_0]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h0, h456, hc12, hc25, hlam, hphi, p609_1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h1, h571, hc35, hlam, hphi, p609_1, u3ehi1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [h573, hlam, p609_1]
                · have p609_0 := h609c.1
                  have p609_1 := h609c.2.1
                  have p609_2 := h609c.2.2.1
                  have p609_3 := h609c.2.2.2
                  linarith only [hlam, p609_0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h641 | h641
            · linarith only [h0, h353, h641, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
              · rcases h0bigk with h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [hlam, p644_0]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  rcases p644_3 (m.d 0 1) (by simp) with h646 | h646
                  · rcases p644_3 (m.d 0 2) (by simp) with h647 | h647
                    · linarith only [h0, h647, hlam]
                    · rcases p644_3 (m.d 0 3) (by simp) with h649 | h649
                      · linarith only [h1, h649, hlam]
                      · linarith only [h4, h649, hlam]
                  · linarith only [h0, h646, hlam]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p644_1, u3ehi1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h1, h495, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p644_1, u3ehi1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h1, h571, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p644_1, u3ehi1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h0, hlam, p644_0]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [hlam, p644_0]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h4, hlam, p644_0]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h353, hlam, p644_1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h456, hlam, p644_0]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h1, hlam, p644_1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h495, h643, hc02, hc23, hlam, hphi, p644_1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [hlam, p644_0]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h495, hlam, p644_1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h571, hlam, p644_1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h2, hlam, p644_0]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h0, h353, hc12, hc24, hlam, hphi, p644_1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h1, h495, h643, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p644_1, u3ehi1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [hlam, p644_0]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h573, hlam, p644_0]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h3, hlam, p644_0]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h0, h456, hc12, hc25, hlam, hphi, p644_1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h1, h571, hc35, hlam, hphi, p644_1, u3ehi1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [h573, hc04, hc45, hlam, hphi, p644_1]
                · have p644_0 := h644c.1
                  have p644_1 := h644c.2.1
                  have p644_2 := h644c.2.2.1
                  have p644_3 := h644c.2.2.2
                  linarith only [hlam, p644_0]
              · rcases h0bigk with h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [hlam, p676_0]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  rcases p676_3 (m.d 0 1) (by simp) with h678 | h678
                  · rcases p676_3 (m.d 0 2) (by simp) with h679 | h679
                    · linarith only [h0, h679, hlam]
                    · rcases p676_3 (m.d 0 3) (by simp) with h681 | h681
                      · linarith only [h1, h681, hlam]
                      · linarith only [h4, h681, hlam]
                  · linarith only [h0, h678, hlam]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p676_1, u3ehi1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h1, h495, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p676_1, u3ehi1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h1, h571, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p676_1, u3ehi1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h0, hlam, p676_0]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [hlam, p676_0]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h4, hlam, p676_0]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h353, hlam, p676_1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h456, hlam, p676_0]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h1, hlam, p676_1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p676_1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [hlam, p676_0]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h495, hlam, p676_1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h571, hlam, p676_1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h2, hlam, p676_0]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h0, h353, h643, hc12, hc34, hlam, hphi, ht23, p676_1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h353, h643, hc34, hlam, hphi, p676_1, u3ehi0]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [hlam, p676_0]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h573, hlam, p676_0]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h3, hlam, p676_0]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h0, h456, hc12, hc25, hlam, hphi, p676_1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h1, h571, hc35, hlam, hphi, p676_1, u3ehi1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [h573, hc04, hc45, hlam, hphi, p676_1]
                · have p676_0 := h676c.1
                  have p676_1 := h676c.2.1
                  have p676_2 := h676c.2.2.1
                  have p676_3 := h676c.2.2.2
                  linarith only [hlam, p676_0]

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h708 | h708
  · rcases m.htr 0 2 4 (by decide) (by decide) with h709 | h709
    · rcases m.htr 0 2 5 (by decide) (by decide) with h710 | h710
      · linarith only [h0, h3, h710, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h712 | h712
        · rcases m.htr 0 3 5 (by decide) (by decide) with h713 | h713
          · linarith only [h0, h3, h708, h713, hlam]
          · linarith only [h712, h713, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h716 | h716
          · linarith only [h712, h716, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h718 | h718
            · linarith only [h0, h3, h709, h718, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h720 | h720
              · rcases m.htr 2 3 4 (by decide) (by decide) with h721 | h721
                · linarith only [h1, h708, h710, h712, h721, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h3, h716, h720, h721, hc35, hlam, hphi, u3ehi2]
              · linarith only [h709, h710, h720, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h725 | h725
      · linarith only [h2, h3, h709, h725, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h727 | h727
        · linarith only [h708, h709, h727, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h729 | h729
          · linarith only [h727, h729, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h731 | h731
            · linarith only [h2, h3, h731, hlam]
            · linarith only [h708, h709, h731, hc45, hlam, hphi, ht34, u3ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h734 | h734
    · rcases m.htr 0 2 5 (by decide) (by decide) with h735 | h735
      · linarith only [h0, h3, h735, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h737 | h737
        · rcases m.htr 0 3 5 (by decide) (by decide) with h738 | h738
          · linarith only [h1, h3, h738, hlam]
          · linarith only [h737, h738, hc35, hlam, hphi, u3ehi3]
        · linarith only [h708, h734, h737, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h742 | h742
      · linarith only [h1, h3, h708, h742, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h744 | h744
        · rcases m.htr 0 3 5 (by decide) (by decide) with h745 | h745
          · linarith only [h1, h3, h745, hlam]
          · linarith only [h744, h745, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h748 | h748
          · linarith only [h744, h748, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h750 | h750
            · linarith only [h2, h3, h750, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h752 | h752
              · linarith only [h0, h734, h752, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h754 | h754
                · rcases h0bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h1, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p755_1, u3ehi1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h3, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h3, hlam, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h0, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h708, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h734, hlam, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h742, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h1, hlam, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h0, h744, h754, hc12, hc23, hlam, hphi, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h744, hlam, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h748, hlam, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h2, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h0, h1, h2, h3, h744, h754, hc12, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p755_1, u3ehi1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h1, h744, h754, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u3ehi1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h750, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h742, hc01, hc25, hlam, hphi, ht12, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h0, h748, hc12, hc35, hlam, hphi, ht23, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h1, h748, hc35, hlam, hphi, p755_1, u3ehi1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h750, hc04, hc45, hlam, hphi, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                · rcases h0bigk with h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [hlam, p781_0]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h0, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p781_1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p781_1, u3ehi1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h1, h744, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p781_1, u3ehi1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h3, hlam, p781_1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h0, hlam, p781_0]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [hlam, p781_0]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h708, hlam, p781_0]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h734, hlam, p781_1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h742, hlam, p781_0]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h1, hlam, p781_1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h0, h1, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p781_1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [hlam, p781_0]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h744, hlam, p781_1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h748, hlam, p781_1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h2, hlam, p781_0]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h0, h2, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p781_1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h2, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p781_1, u3ehi0]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [hlam, p781_0]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h750, hlam, p781_0]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h750, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p781_1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h0, h750, hc12, hc45, hlam, hphi, ht23, ht34, p781_1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h1, h750, hc45, hlam, hphi, ht34, p781_1, u3ehi1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [h750, hc04, hc45, hlam, hphi, p781_1]
                  · have p781_0 := h781c.1
                    have p781_1 := h781c.2.1
                    have p781_2 := h781c.2.2.1
                    have p781_3 := h781c.2.2.2
                    linarith only [hlam, p781_0]

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2 h3
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2 h3

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h807 | h807
  · rcases m.htr 0 2 3 (by decide) (by decide) with h808 | h808
    · rcases m.htr 0 2 4 (by decide) (by decide) with h809 | h809
      · linarith only [h0, h2, h809, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h811 | h811
        · rcases m.htr 0 3 4 (by decide) (by decide) with h812 | h812
          · linarith only [h0, h2, h808, h812, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h814 | h814
            · linarith only [h812, h814, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h816 | h816
              · rcases m.htr 1 2 4 (by decide) (by decide) with h817 | h817
                · linarith only [h0, h2, h809, h817, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h819 | h819
                  · linarith only [h0, h2, h808, h817, h819, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h2, h808, h817, h819, hc34, hlam, hphi, u3ehi2]
              · linarith only [h0, h2, h808, h816, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h823 | h823
          · linarith only [h2, h807, h808, h811, h823, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h825 | h825
            · linarith only [h823, h825, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h827 | h827
              · rcases m.htr 1 2 4 (by decide) (by decide) with h828 | h828
                · linarith only [h0, h2, h809, h828, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h830 | h830
                  · linarith only [h808, h823, h830, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h2, h807, h808, h811, h828, h830, hc34, hlam, hphi, u3ehi2]
              · linarith only [h2, h807, h808, h811, h827, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h834 | h834
      · linarith only [h0, h2, h834, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h836 | h836
        · rcases m.htr 0 3 4 (by decide) (by decide) with h837 | h837
          · linarith only [h1, h2, h837, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h839 | h839
            · linarith only [h837, h839, hc34, hlam, hphi, u3ehi4]
            · linarith only [h808, h836, h839, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h842 | h842
          · linarith only [h1, h2, h842, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h844 | h844
            · linarith only [h842, h844, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h846 | h846
              · rcases m.htr 1 2 4 (by decide) (by decide) with h847 | h847
                · linarith only [h0, h2, h834, h847, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h849 | h849
                  · rcases h0bigk with h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [hlam, p850_0]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h1, h2, h847, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p850_1, u3ehi1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h2, hlam, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h1, h2, h842, h844, h849, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p850_1, u3ehi1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h0, hlam, p850_0]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [hlam, p850_0]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h808, hlam, p850_0]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h834, hlam, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h836, hlam, p850_0]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h1, hlam, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h0, h844, hc12, hc35, hlam, hphi, ht23, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [hlam, p850_0]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h842, hlam, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h844, hlam, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h842, h849, hc01, hc23, hlam, hphi, ht12, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h0, h842, h849, hc12, hc23, hlam, hphi, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h842, h849, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p850_1, u3ehi0]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [hlam, p850_0]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h842, h849, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h807, hlam, p850_0]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h0, h2, h807, h842, h849, hc12, hc23, hlam, hphi, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h1, h2, h807, h842, h849, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p850_1, u3ehi1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [h846, hlam, p850_1]
                    · have p850_0 := h850c.1
                      have p850_1 := h850c.2.1
                      have p850_2 := h850c.2.2.1
                      have p850_3 := h850c.2.2.2
                      linarith only [hlam, p850_0]
                  · linarith only [h1, h2, h847, h849, hc34, hlam, hphi, u3ehi1]
              · linarith only [h1, h2, h846, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h878 | h878
    · rcases m.htr 0 2 4 (by decide) (by decide) with h879 | h879
      · linarith only [h0, h2, h879, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h881 | h881
        · linarith only [h0, h807, h881, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h883 | h883
          · linarith only [h0, h2, h878, h883, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h885 | h885
            · linarith only [h883, h885, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h887 | h887
              · rcases m.htr 1 2 4 (by decide) (by decide) with h888 | h888
                · linarith only [h0, h2, h879, h888, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h890 | h890
                  · linarith only [h878, h883, h890, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1, h2, h888, h890, hc34, hlam, hphi, u3ehi1]
              · linarith only [h0, h2, h878, h887, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h894 | h894
      · linarith only [h1, h2, h878, h894, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h896 | h896
        · linarith only [h1, h807, h878, h896, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h898 | h898
          · linarith only [h1, h2, h898, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h900 | h900
            · linarith only [h898, h900, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h902 | h902
              · rcases m.htr 1 2 4 (by decide) (by decide) with h903 | h903
                · linarith only [h0, h2, h894, h903, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h905 | h905
                  · rcases h0bigk with h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [hlam, p906_0]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h0, h807, h898, h902, h905, hc12, hc23, hlam, hphi, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h807, h898, h902, h905, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p906_1, u3ehi0]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h2, hlam, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h807, hlam, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h0, hlam, p906_0]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [hlam, p906_0]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h878, hlam, p906_0]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h894, hlam, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h896, hlam, p906_0]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h1, hlam, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h0, h900, hc12, hc35, hlam, hphi, ht23, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [hlam, p906_0]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h898, hlam, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h900, hlam, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h1, h898, h905, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p906_1, u3ehi1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h0, h898, h905, hc12, hc23, hlam, hphi, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h898, h905, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p906_1, u3ehi0]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [hlam, p906_0]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h898, h905, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p906_1, u3ehi1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h0, h896, hc12, hc25, hlam, hphi, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h1, h900, hc35, hlam, hphi, p906_1, u3ehi1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [h902, hlam, p906_1]
                    · have p906_0 := h906c.1
                      have p906_1 := h906c.2.1
                      have p906_2 := h906c.2.2.1
                      have p906_3 := h906c.2.2.2
                      linarith only [hlam, p906_0]
                  · linarith only [h1, h2, h903, h905, hc34, hlam, hphi, u3ehi1]
              · linarith only [h1, h2, h902, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2

end R2N4
