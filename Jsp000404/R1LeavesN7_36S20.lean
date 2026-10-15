import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_36S16
import Jsp000404.R1LeavesN7_36S17
import Jsp000404.R1LeavesN7_36S18
import Jsp000404.R1LeavesN7_36S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2006 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2517 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2655 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2877 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h3333 | h3333
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3334 | h3334
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3335 | h3335
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3336 | h3336
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3337 | h3337
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3338 | h3338
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3339 | h3339
              · rcases h0bigk with h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [hlam, p3340_0]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h0, hlam, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2006, hlam, p3340_0]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2517, hlam, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2655, hlam, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [hlam, p3340_0]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2877, hlam, p3340_0]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2877, h3335, h3339, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3340_1, u4ehi4]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2877, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2006, hc01, hc13, hlam, hphi, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2877, hc02, hc23, hlam, hphi, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [hlam, p3340_0]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2877, h3335, h3339, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3340_1, u4ehi4]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2655, h2877, hc01, hc23, hlam, hphi, ht12, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h0, h3333, hc01, hc12, hlam, hphi, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h3333, hlam, p3340_0]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h3335, hlam, p3340_0]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [hlam, p3340_0]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2655, h2877, h3333, hc01, hc23, hlam, hphi, ht12, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h2655, h3338, hc01, hc14, hlam, hphi, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h3334, hlam, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h3336, hlam, p3340_0]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [h3337, hlam, p3340_1]
                · have p3340_0 := h3340c.1
                  have p3340_1 := h3340c.2.1
                  have p3340_2 := h3340c.2.2.1
                  have p3340_3 := h3340c.2.2.2
                  linarith only [hlam, p3340_0]
              · linarith only [h2877, h3333, h3337, h3339, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · linarith only [h2877, h3333, h3337, h3338, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3368 | h3368
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3369 | h3369
              · linarith only [h2877, h3333, h3335, h3337, h3369, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases h0bigk with h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [hlam, p3371_0]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h0, hlam, p3371_1]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2006, hlam, p3371_0]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2517, hlam, p3371_1]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2655, hlam, p3371_1]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3371_1]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [hlam, p3371_0]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2877, hlam, p3371_0]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2877, h3333, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3371_1, u4ehi2]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2877, h3333, h3337, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3371_1, u4ehi2]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3371_1]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2877, hc02, hc23, hlam, hphi, p3371_1]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [hlam, p3371_0]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2877, h3333, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3371_1, u4ehi2]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2877, h3333, h3337, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3371_1, u4ehi2]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h3337, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3371_1]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h3333, hlam, p3371_0]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h3335, hlam, p3371_0]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [hlam, p3371_0]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h3337, hlam, p3371_0]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3371_1]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h3334, hlam, p3371_1]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h3336, hlam, p3371_0]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [h3334, hc02, hlam, hphi, ht0b, ht45, ht5b, p3371_1, u4ehi0]
                · have p3371_0 := h3371c.1
                  have p3371_1 := h3371c.2.1
                  have p3371_2 := h3371c.2.2.1
                  have p3371_3 := h3371c.2.2.2
                  linarith only [hlam, p3371_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3397 | h3397
              · linarith only [h2517, h3368, h3397, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases h0bigk with h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [hlam, p3399_0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h0, hlam, p3399_1]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2006, hlam, p3399_0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2517, hlam, p3399_1]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2655, hlam, p3399_1]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3399_1]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [hlam, p3399_0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2877, hlam, p3399_0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2877, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3399_1, u4ehi0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2877, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3399_1]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3399_1]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2877, hc02, hc23, hlam, hphi, p3399_1]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [hlam, p3399_0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2877, h3335, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3399_1, u4ehi3]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2655, h2877, hc01, hc23, hlam, hphi, ht12, p3399_1]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3399_1]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h3333, hlam, p3399_0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h3335, hlam, p3399_0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [hlam, p3399_0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h3337, hlam, p3399_0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3399_1]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h3334, hlam, p3399_1]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h3336, hlam, p3399_0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [h2877, h3334, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3399_1, u4ehi0]
                · have p3399_0 := h3399c.1
                  have p3399_1 := h3399c.2.1
                  have p3399_2 := h3399c.2.2.1
                  have p3399_3 := h3399c.2.2.2
                  linarith only [hlam, p3399_0]
        · linarith only [h2877, h3334, h3336, hlam]
      · linarith only [h2877, h3333, h3335, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3427 | h3427
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3428 | h3428
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3429 | h3429
          · linarith only [h3333, h3334, h3429, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3431 | h3431
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3432 | h3432
              · linarith only [h3427, h3429, h3432, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases h0bigk with h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [hlam, p3434_0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h0, hlam, p3434_1]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h2006, hlam, p3434_0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h2517, hlam, p3434_1]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h2655, hlam, p3434_1]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h3334, h3429, h3431, hc01, hc14, hlam, hphi, p3434_1]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [hlam, p3434_0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h2877, hlam, p3434_0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h3333, h3334, h3429, h3431, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3434_1, u4ehi2]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h3334, hlam, p3434_0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3434_1]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h2877, hc02, hc23, hlam, hphi, p3434_1]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [hlam, p3434_0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h2877, h3333, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3434_1, u4ehi2]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h2655, h2877, hc01, hc23, hlam, hphi, ht12, p3434_1]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3434_1]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h3333, hlam, p3434_0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h3427, hlam, p3434_0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [hlam, p3434_0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h3429, hlam, p3434_0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h2655, h3431, hc01, hc14, hlam, hphi, p3434_1]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h2655, h3333, h3431, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3434_1, u4ehi2]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h3428, hlam, p3434_0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [h3429, h3431, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3434_1, u4ehi0]
                · have p3434_0 := h3434c.1
                  have p3434_1 := h3434c.2.1
                  have p3434_2 := h3434c.2.2.1
                  have p3434_3 := h3434c.2.2.2
                  linarith only [hlam, p3434_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3460 | h3460
              · linarith only [h2517, h3431, h3460, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases h0bigk with h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c | h3462c
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [hlam, p3462_0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h0, hlam, p3462_1]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h2006, hlam, p3462_0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h2517, hlam, p3462_1]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h2655, hlam, p3462_1]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3462_1]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [hlam, p3462_0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h2877, hlam, p3462_0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h2877, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3462_1, u4ehi0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h3334, hlam, p3462_0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3462_1]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h2877, hc02, hc23, hlam, hphi, p3462_1]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [hlam, p3462_0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h2877, h3427, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3462_1, u4ehi3]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h2655, h2877, hc01, hc23, hlam, hphi, ht12, p3462_1]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3462_1]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h3333, hlam, p3462_0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h3427, hlam, p3462_0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [hlam, p3462_0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h3429, hlam, p3462_0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3462_1]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h3333, h3334, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3462_1, u4ehi2]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h3428, hlam, p3462_0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [h3429, hc45, hlam, hphi, p3462_1, u4ehi0]
                · have p3462_0 := h3462c.1
                  have p3462_1 := h3462c.2.1
                  have p3462_2 := h3462c.2.2.1
                  have p3462_3 := h3462c.2.2.2
                  linarith only [hlam, p3462_0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3488 | h3488
          · linarith only [h3333, h3334, h3488, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3490 | h3490
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3491 | h3491
              · linarith only [h3427, h3428, h3488, h3491, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
              · linarith only [h2877, h3333, h3428, h3491, hc45, hlam, hphi, u4ehi2]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3494 | h3494
              · linarith only [h2517, h3490, h3494, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h2877, h3333, h3428, h3494, hc45, hlam, hphi, u4ehi2]
      · linarith only [h2877, h3333, h3427, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3498 | h3498
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3499 | h3499
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3500 | h3500
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3501 | h3501
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3502 | h3502
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3503 | h3503
              · rcases h0bigk with h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c | h3504c
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h0, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2006, hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2517, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2655, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3333, hc01, hc24, hlam, hphi, ht12, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2877, hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3333, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3500, h3503, hc02, hlam, hphi, ht0b, ht45, ht5b, p3504_1, u4ehi4]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2006, hc01, hc13, hlam, hphi, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2877, hc02, hc23, hlam, hphi, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2877, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3504_1, u4ehi0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2877, h3500, h3503, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3504_1, u4ehi4]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3333, h3498, h3500, h3503, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3504_1, u4ehi4]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3499, hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h2877, h3499, h3500, h3503, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3504_1, u4ehi4]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h0, h3498, hc01, hc12, hlam, hphi, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3498, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3500, hlam, p3504_0]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [h3501, hlam, p3504_1]
                · have p3504_0 := h3504c.1
                  have p3504_1 := h3504c.2.1
                  have p3504_2 := h3504c.2.2.1
                  have p3504_3 := h3504c.2.2.2
                  linarith only [hlam, p3504_0]
              · rcases h0bigk with h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [hlam, p3530_0]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h0, hlam, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2006, hlam, p3530_0]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2517, hlam, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2655, hlam, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [hlam, p3530_0]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2877, hlam, p3530_0]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h3333, hlam, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2877, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2877, hc02, hc23, hlam, hphi, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [hlam, p3530_0]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2877, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3530_1, u4ehi0]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2655, h2877, hc01, hc23, hlam, hphi, ht12, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h3333, h3498, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h3499, hlam, p3530_0]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [hlam, p3530_0]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2655, h2877, h3499, hc01, hc23, hlam, hphi, ht12, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h2655, h3502, hc01, hc14, hlam, hphi, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h3498, hlam, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h3500, hlam, p3530_0]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [h3501, hlam, p3530_1]
                · have p3530_0 := h3530c.1
                  have p3530_1 := h3530c.2.1
                  have p3530_2 := h3530c.2.2.1
                  have p3530_3 := h3530c.2.2.2
                  linarith only [hlam, p3530_0]
            · linarith only [h2517, h3501, h3502, hlam]
          · linarith only [h3333, h3498, h3501, hlam]
        · linarith only [h2877, h3498, h3500, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3559 | h3559
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3560 | h3560
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3561 | h3561
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3562 | h3562
              · rcases h0bigk with h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [hlam, p3563_0]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h0, hlam, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h2006, hlam, p3563_0]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h2517, hlam, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h2655, hlam, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h2517, h2877, h3499, hc01, hc14, hlam, hphi, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [hlam, p3563_0]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h2877, hlam, p3563_0]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h3333, hlam, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h2877, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h3499, hc01, hc34, hlam, hphi, ht12, ht23, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h3499, hc02, hc34, hlam, hphi, ht23, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [hlam, p3563_0]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h3499, hlam, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h2655, h3499, hc01, hc34, hlam, hphi, ht12, ht23, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h3499, hc01, hc34, hlam, hphi, ht12, ht23, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h3498, h3499, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h3499, h3559, h3562, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3563_1, u4ehi4]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [hlam, p3563_0]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h3499, h3559, h3562, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3563_1, u4ehi4]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h0, h3498, hc01, hc12, hlam, hphi, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h3498, hlam, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h3559, hlam, p3563_0]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [h3560, hlam, p3563_1]
                · have p3563_0 := h3563c.1
                  have p3563_1 := h3563c.2.1
                  have p3563_2 := h3563c.2.2.1
                  have p3563_3 := h3563c.2.2.2
                  linarith only [hlam, p3563_0]
              · linarith only [h3499, h3560, h3562, hlam]
            · linarith only [h2517, h2877, h3498, h3499, h3560, h3561, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h2877, h3498, h3499, h3560, hlam]
        · linarith only [h2877, h3498, h3559, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3593 | h3593
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3594 | h3594
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3595 | h3595
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3596 | h3596
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3597 | h3597
              · rcases h0bigk with h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [hlam, p3598_0]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h0, hlam, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h2006, hlam, p3598_0]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h2517, hlam, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h2655, hlam, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h3498, hc01, hc25, hlam, hphi, ht12, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [hlam, p3598_0]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h2877, hlam, p3598_0]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h3333, hlam, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h3498, hlam, p3598_0]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h2006, hc01, hc13, hlam, hphi, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h2877, hc02, hc23, hlam, hphi, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [hlam, p3598_0]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h2877, h3593, h3597, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3598_1, u4ehi4]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h0, h2877, h3498, hc01, hc23, hlam, hphi, ht12, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h0, h3333, hc01, hc24, hlam, hphi, ht12, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h3593, hlam, p3598_0]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [hlam, p3598_0]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h0, h2877, h3498, h3593, hc01, hc23, hlam, hphi, ht12, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h0, h3498, hc01, hc25, hlam, hphi, ht12, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h3594, hlam, p3598_0]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [h3595, hlam, p3598_1]
                · have p3598_0 := h3598c.1
                  have p3598_1 := h3598c.2.1
                  have p3598_2 := h3598c.2.2.1
                  have p3598_3 := h3598c.2.2.2
                  linarith only [hlam, p3598_0]
              · rcases h0bigk with h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c | h3624c
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [hlam, p3624_0]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h0, hlam, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h2006, hlam, p3624_0]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h2517, hlam, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h2655, hlam, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [hlam, p3624_0]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h2877, hlam, p3624_0]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h3333, hlam, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h3498, hlam, p3624_0]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h2877, hc02, hc23, hlam, hphi, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [hlam, p3624_0]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h2877, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3624_1, u4ehi0]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h2655, h2877, hc01, hc23, hlam, hphi, ht12, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h0, h3333, hc01, hc24, hlam, hphi, ht12, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h3593, hlam, p3624_0]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [hlam, p3624_0]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h0, h2877, h3498, h3593, hc01, hc23, hlam, hphi, ht12, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h2655, h3596, hc01, hc14, hlam, hphi, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h0, h2655, h3596, hc01, hc14, hlam, hphi, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h3594, hlam, p3624_0]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [h3595, hlam, p3624_1]
                · have p3624_0 := h3624c.1
                  have p3624_1 := h3624c.2.1
                  have p3624_2 := h3624c.2.2.1
                  have p3624_3 := h3624c.2.2.2
                  linarith only [hlam, p3624_0]
            · linarith only [h2517, h3595, h3596, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3651 | h3651
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3652 | h3652
              · linarith only [h2877, h3593, h3595, h3652, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
              · rcases h0bigk with h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [hlam, p3654_0]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h0, hlam, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h2006, hlam, p3654_0]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h2517, hlam, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h2655, hlam, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [hlam, p3654_0]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h2877, hlam, p3654_0]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h3333, hlam, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h3498, hlam, p3654_0]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h2877, hc02, hc23, hlam, hphi, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [hlam, p3654_0]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h2877, h3593, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3654_1, u4ehi3]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h2655, h2877, hc01, hc23, hlam, hphi, ht12, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h0, h3333, hc01, hc24, hlam, hphi, ht12, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h3593, hlam, p3654_0]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [hlam, p3654_0]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h3595, hlam, p3654_0]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h0, h3498, hc01, hc25, hlam, hphi, ht12, p3654_1]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h3594, hlam, p3654_0]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [h3595, hc45, hlam, hphi, p3654_1, u4ehi0]
                · have p3654_0 := h3654c.1
                  have p3654_1 := h3654c.2.1
                  have p3654_2 := h3654c.2.2.1
                  have p3654_3 := h3654c.2.2.2
                  linarith only [hlam, p3654_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3680 | h3680
              · linarith only [h2517, h3651, h3680, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases h0bigk with h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [hlam, p3682_0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h0, hlam, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h2006, hlam, p3682_0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h2517, hlam, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h2655, hlam, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [hlam, p3682_0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h2877, hlam, p3682_0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h3333, hlam, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h3498, hlam, p3682_0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h2877, hc01, hc23, hlam, hphi, ht12, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h2877, hc02, hc23, hlam, hphi, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [hlam, p3682_0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h2877, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3682_1, u4ehi0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h2655, h2877, hc01, hc23, hlam, hphi, ht12, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h0, h2517, h3651, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h3593, hlam, p3682_0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [hlam, p3682_0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h3595, hlam, p3682_0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h0, h3498, hc01, hc25, hlam, hphi, ht12, p3682_1]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h3594, hlam, p3682_0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [h3595, hc45, hlam, hphi, p3682_1, u4ehi0]
                · have p3682_0 := h3682c.1
                  have p3682_1 := h3682c.2.1
                  have p3682_2 := h3682c.2.2.1
                  have p3682_3 := h3682c.2.2.2
                  linarith only [hlam, p3682_0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3708 | h3708
          · linarith only [h3593, h3594, h3708, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3710 | h3710
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3711 | h3711
              · linarith only [h3593, h3594, h3708, h3711, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
              · linarith only [h3593, h3594, h3711, hc45, hlam, hphi, u4ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3714 | h3714
              · linarith only [h3593, h3710, h3714, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h3593, h3594, h3714, hc45, hlam, hphi, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3717 | h3717
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3718 | h3718
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3719 | h3719
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3720 | h3720
              · rcases h0bigk with h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [hlam, p3721_0]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h0, hlam, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h2006, hlam, p3721_0]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h2517, hlam, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h2655, hlam, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [hlam, p3721_0]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h2877, hlam, p3721_0]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h3333, hlam, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h3498, hlam, p3721_0]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h3593, hc01, hc34, hlam, hphi, ht12, ht23, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h3593, hc02, hc34, hlam, hphi, ht23, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [hlam, p3721_0]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h3593, hlam, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h3593, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h0, h3333, hc01, hc24, hlam, hphi, ht12, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h3593, h3717, h3720, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3721_1, u4ehi4]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [hlam, p3721_0]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h3593, h3717, h3720, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3721_1, u4ehi4]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h0, h3498, hc01, hc25, hlam, hphi, ht12, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h3717, hlam, p3721_0]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [h3718, hlam, p3721_1]
                · have p3721_0 := h3721c.1
                  have p3721_1 := h3721c.2.1
                  have p3721_2 := h3721c.2.2.1
                  have p3721_3 := h3721c.2.2.2
                  linarith only [hlam, p3721_0]
              · linarith only [h3593, h3718, h3720, hlam]
            · linarith only [h2517, h3593, h3717, h3718, h3719, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h3593, h3717, h3718, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3750 | h3750
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3751 | h3751
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3752 | h3752
              · rcases h0bigk with h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [hlam, p3753_0]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h0, hlam, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h2006, hlam, p3753_0]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h2517, hlam, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h2655, hlam, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [hlam, p3753_0]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h2877, hlam, p3753_0]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h3333, hlam, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h3498, hlam, p3753_0]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h3717, hc01, hc35, hlam, hphi, ht12, ht23, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h3717, hc02, hc35, hlam, hphi, ht23, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [hlam, p3753_0]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h3593, hlam, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h3717, hlam, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h0, h3333, hc01, hc24, hlam, hphi, ht12, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h3593, hc03, hc34, hlam, hphi, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [hlam, p3753_0]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h0, h2877, h3593, h3717, hc01, hc34, hlam, hphi, ht12, ht23, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h0, h3498, hc01, hc25, hlam, hphi, ht12, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h0, h2877, h3717, hc01, hc35, hlam, hphi, ht12, ht23, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [h3750, hlam, p3753_1]
                · have p3753_0 := h3753c.1
                  have p3753_1 := h3753c.2.1
                  have p3753_2 := h3753c.2.2.1
                  have p3753_3 := h3753c.2.2.2
                  linarith only [hlam, p3753_0]
              · linarith only [h3593, h3750, h3752, hlam]
            · linarith only [h2517, h3593, h3750, h3751, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3781 | h3781
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3782 | h3782
              · rcases h0bigk with h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c | h3783c
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [hlam, p3783_0]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h0, hlam, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h2006, hlam, p3783_0]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h2517, hlam, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h2655, hlam, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [hlam, p3783_0]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h2877, hlam, p3783_0]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h3333, hlam, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h3498, hlam, p3783_0]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h2006, hc01, hc13, hlam, hphi, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h0, h2006, hc01, hc13, hlam, hphi, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [hlam, p3783_0]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h3593, hlam, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h3717, hlam, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h3750, h3782, hc01, hc34, hlam, hphi, ht12, ht23, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h0, h3750, h3782, hc01, hc34, hlam, hphi, ht12, ht23, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h3750, h3782, hc03, hc34, hlam, hphi, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [hlam, p3783_0]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h3750, hlam, p3783_0]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h3750, h3782, hc01, hc34, hlam, hphi, ht12, ht23, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h0, h3750, h3782, hc01, hc34, hlam, hphi, ht12, ht23, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h0, h2877, h3750, h3782, hc01, hc34, hlam, hphi, ht12, ht23, p3783_1]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [h3750, h3782, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3783_1, u4ehi0]
                · have p3783_0 := h3783c.1
                  have p3783_1 := h3783c.2.1
                  have p3783_2 := h3783c.2.2.1
                  have p3783_3 := h3783c.2.2.2
                  linarith only [hlam, p3783_0]
              · linarith only [h0, h2877, h3593, h3781, h3782, hc01, hc14, hlam, hphi]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3810 | h3810
              · linarith only [h2517, h3781, h3810, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases h0bigk with h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c | h3812c
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [hlam, p3812_0]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h0, hlam, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h2006, hlam, p3812_0]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h2517, hlam, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h2655, hlam, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h2877, h3593, hc01, hc34, hlam, hphi, ht12, ht23, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [hlam, p3812_0]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h2877, hlam, p3812_0]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h3333, hlam, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h3498, hlam, p3812_0]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h3593, h3810, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h3593, h3810, hc02, hc45, hlam, hphi, ht23, ht34, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [hlam, p3812_0]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h3593, hlam, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h3717, hlam, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h0, h3333, hc01, hc24, hlam, hphi, ht12, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h3593, h3810, hc03, hc45, hlam, hphi, ht34, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [hlam, p3812_0]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h3750, hlam, p3812_0]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h0, h3498, hc01, hc25, hlam, hphi, ht12, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h0, h2877, h3717, hc01, hc35, hlam, hphi, ht12, ht23, p3812_1]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [h3750, hc45, hlam, hphi, p3812_1, u4ehi0]
                · have p3812_0 := h3812c.1
                  have p3812_1 := h3812c.2.1
                  have p3812_2 := h3812c.2.2.1
                  have p3812_3 := h3812c.2.2.2
                  linarith only [hlam, p3812_0]

set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2006 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2517 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2655 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h2877 | h2877
  · exact r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x1_x1_x0 m hb0 hb2 hb4 h0 h2006 h2517 h2655 h2877
  · exact r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x1_x1_x1 m hb0 hb2 hb4 h0 h2006 h2517 h2655 h2877

set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2006 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2517 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h2655 | h2655
  · exact r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x1_x0 m hb0 hb2 hb4 h0 h2006 h2517 h2655
  · exact r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x1_x1 m hb0 hb2 hb4 h0 h2006 h2517 h2655

set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2006 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h2517 | h2517
  · exact r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x0 m hb0 hb2 hb4 h0 h2006 h2517
  · exact r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x1 m hb0 hb2 hb4 h0 h2006 h2517

set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h2006 | h2006
  · exact r1l7_20_12_14_H_I_L_I_L_R_x1_x0 m hb0 hb2 hb4 h0 h2006
  · exact r1l7_20_12_14_H_I_L_I_L_R_x1_x1 m hb0 hb2 hb4 h0 h2006

set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_H_I_L_I_L_R_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_H_I_L_I_L_R_x1 m hb0 hb2 hb4 h0

end R2N4
