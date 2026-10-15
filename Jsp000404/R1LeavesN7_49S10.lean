import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_49S8
import Jsp000404.R1LeavesN7_49S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1337 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1673 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1959 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2140 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h2356 | h2356
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2357 | h2357
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2358 | h2358
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2359 | h2359
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2360 | h2360
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2361 | h2361
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2362 | h2362
              · rcases h0bigk with h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [hlam, p2363_0]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h0, hlam, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h1337, hlam, p2363_0]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h1673, hlam, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h1959, hlam, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [hlam, p2363_0]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h2140, hlam, p2363_0]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h2140, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h2140, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h2140, h2356, h2362, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2363_1, u3ehi3]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [hlam, p2363_0]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h2140, h2356, h2362, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2363_1, u3ehi3]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h1959, h2140, hc01, hc23, hlam, hphi, ht12, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h1673, h2361, hc01, hc12, hlam, hphi, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h2356, hlam, p2363_0]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h2358, hlam, p2363_0]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [hlam, p2363_0]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h2356, h2359, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p2363_1, u3ehi4]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h2357, hlam, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h2359, hlam, p2363_0]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [h2360, hlam, p2363_1]
                · have p2363_0 := h2363c.1
                  have p2363_1 := h2363c.2.1
                  have p2363_2 := h2363c.2.2.1
                  have p2363_3 := h2363c.2.2.2
                  linarith only [hlam, p2363_0]
              · linarith only [h2140, h2358, h2362, hlam]
            · linarith only [h2140, h2356, h2361, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2391 | h2391
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2392 | h2392
              · rcases h0bigk with h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c | h2393c
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [hlam, p2393_0]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h0, hlam, p2393_1]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h1337, hlam, p2393_0]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h1673, hlam, p2393_1]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h1959, hlam, p2393_1]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2140, hc01, hc23, hlam, hphi, ht12, p2393_1]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [hlam, p2393_0]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2140, hlam, p2393_0]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2140, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2393_1]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2140, h2356, h2360, h2392, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2393_1, u3ehi3]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2140, hc01, hc23, hlam, hphi, ht12, p2393_1]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2140, hc02, hc23, hlam, hphi, p2393_1]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [hlam, p2393_0]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2140, h2356, h2392, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2393_1, u3ehi3]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2140, h2356, h2360, h2392, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2393_1, u3ehi3]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2360, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2393_1]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2356, hlam, p2393_0]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2358, hlam, p2393_0]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [hlam, p2393_0]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2360, hlam, p2393_0]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2393_1]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2357, hlam, p2393_1]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2359, hlam, p2393_0]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [h2140, h2357, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2393_1]
                · have p2393_0 := h2393c.1
                  have p2393_1 := h2393c.2.1
                  have p2393_2 := h2393c.2.2.1
                  have p2393_3 := h2393c.2.2.2
                  linarith only [hlam, p2393_0]
              · linarith only [h2140, h2357, h2359, h2392, hc34, hlam, hphi, u3ehi4]
            · linarith only [h2140, h2356, h2391, hc12, hc23, hlam, hphi]
        · linarith only [h2358, h2359, hc35, hlam, hphi, u3ehi3]
      · linarith only [h2140, h2356, h2358, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2423 | h2423
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2424 | h2424
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2425 | h2425
          · linarith only [h2356, h2357, h2425, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2427 | h2427
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2428 | h2428
              · rcases h0bigk with h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [hlam, p2429_0]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h0, hlam, p2429_1]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h1337, hlam, p2429_0]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h1673, hlam, p2429_1]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h1959, hlam, p2429_1]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2140, hc01, hc23, hlam, hphi, ht12, p2429_1]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [hlam, p2429_0]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2140, hlam, p2429_0]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2140, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2429_1]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2357, hlam, p2429_0]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2429_1]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2140, hc02, hc23, hlam, hphi, p2429_1]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [hlam, p2429_0]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h1673, h2140, hc01, hc23, hlam, hphi, ht12, p2429_1]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2140, h2356, h2357, h2423, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2429_1, u3ehi3]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2356, h2357, hc01, hc25, hlam, hphi, ht12, p2429_1]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2356, hlam, p2429_0]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2423, hlam, p2429_0]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [hlam, p2429_0]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2425, hlam, p2429_0]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2429_1]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2357, hc02, hc25, hlam, hphi, p2429_1]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2424, hlam, p2429_0]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [h2423, h2425, hc45, hlam, hphi, ht34, p2429_1, u3ehi3]
                · have p2429_0 := h2429c.1
                  have p2429_1 := h2429c.2.1
                  have p2429_2 := h2429c.2.2.1
                  have p2429_3 := h2429c.2.2.2
                  linarith only [hlam, p2429_0]
              · linarith only [h2140, h2424, h2428, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h2356, h2427, hlam]
        · linarith only [h2423, h2424, hc35, hlam, hphi, u3ehi3]
      · linarith only [h2140, h2356, h2423, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2459 | h2459
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2460 | h2460
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2461 | h2461
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2462 | h2462
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2463 | h2463
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2464 | h2464
              · rcases h0bigk with h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [hlam, p2465_0]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h0, hlam, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h1337, hlam, p2465_0]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h1673, hlam, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h1959, hlam, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2356, h2463, hc01, hc12, hlam, hphi, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [hlam, p2465_0]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2140, hlam, p2465_0]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2356, hlam, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2356, h2461, h2463, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2465_1, u3ehi4]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2140, hc02, hc23, hlam, hphi, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [hlam, p2465_0]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2140, h2462, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2140, h2461, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2465_1, u3ehi4]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h1673, hc01, hc14, hlam, hphi, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2356, h2459, h2461, h2463, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2465_1, u3ehi4]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2460, hlam, p2465_0]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [hlam, p2465_0]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2356, h2461, h2463, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2465_1, u3ehi4]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h0, h2459, hc01, hc12, hlam, hphi, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2459, hlam, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2461, hlam, p2465_0]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [h2462, hlam, p2465_1]
                · have p2465_0 := h2465c.1
                  have p2465_1 := h2465c.2.1
                  have p2465_2 := h2465c.2.2.1
                  have p2465_3 := h2465c.2.2.2
                  linarith only [hlam, p2465_0]
              · linarith only [h2140, h2460, h2464, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2492 | h2492
              · rcases h0bigk with h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [hlam, p2493_0]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h0, hlam, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h1337, hlam, p2493_0]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h1673, hlam, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h1959, hlam, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [hlam, p2493_0]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h2140, hlam, p2493_0]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h2356, hlam, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h0, h2461, h2463, h2492, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2493_1, u3ehi4]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h2140, hc01, hc23, hlam, hphi, ht12, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h2140, hc02, hc23, hlam, hphi, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [hlam, p2493_0]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h1673, h2140, hc01, hc23, hlam, hphi, ht12, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h2140, h2461, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2493_1, u3ehi4]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h1673, hc01, hc14, hlam, hphi, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h2356, h2459, h2461, h2492, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2493_1, u3ehi4]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h2460, hlam, p2493_0]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [hlam, p2493_0]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h2356, h2461, h2492, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2493_1, u3ehi4]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h0, h2459, h2463, h2492, hc01, hc23, hlam, hphi, ht12, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h2459, hlam, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h2461, hlam, p2493_0]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [h2462, hlam, p2493_1]
                · have p2493_0 := h2493c.1
                  have p2493_1 := h2493c.2.1
                  have p2493_2 := h2493c.2.2.1
                  have p2493_3 := h2493c.2.2.2
                  linarith only [hlam, p2493_0]
              · linarith only [h2140, h2460, h2492, hlam]
          · linarith only [h2356, h2459, h2462, hlam]
        · linarith only [h2460, h2461, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2522 | h2522
        · linarith only [h2460, h2522, hc34, hlam, hphi, u3ehi4]
        · linarith only [h2140, h2459, h2522, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2525 | h2525
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2526 | h2526
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2527 | h2527
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2528 | h2528
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2529 | h2529
              · rcases h0bigk with h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [hlam, p2530_0]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h0, hlam, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h1337, hlam, p2530_0]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h1673, hlam, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h1959, hlam, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h2459, hc01, hc25, hlam, hphi, ht12, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [hlam, p2530_0]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h2140, hlam, p2530_0]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h2356, hlam, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h2459, hlam, p2530_0]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h2140, hc02, hc23, hlam, hphi, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [hlam, p2530_0]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h2140, h2526, h2527, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2530_1, u3ehi4]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h2140, h2526, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2530_1, u3ehi4]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h1673, hc01, hc14, hlam, hphi, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h0, h2356, h2528, hc01, hc12, hlam, hphi, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h2525, hlam, p2530_0]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [hlam, p2530_0]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h2356, h2526, h2528, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2530_1, u3ehi4]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h0, h2459, hc01, hc25, hlam, hphi, ht12, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h2526, hlam, p2530_0]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [h2527, hlam, p2530_1]
                · have p2530_0 := h2530c.1
                  have p2530_1 := h2530c.2.1
                  have p2530_2 := h2530c.2.2.1
                  have p2530_3 := h2530c.2.2.2
                  linarith only [hlam, p2530_0]
              · linarith only [h2140, h2525, h2529, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2557 | h2557
              · rcases h0bigk with h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [hlam, p2558_0]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h0, hlam, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h1337, hlam, p2558_0]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h1673, hlam, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h1959, hlam, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h0, h2528, h2557, hc01, hc23, hlam, hphi, ht12, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [hlam, p2558_0]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h2140, hlam, p2558_0]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h2356, hlam, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h2459, hlam, p2558_0]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h2140, hc02, hc23, hlam, hphi, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [hlam, p2558_0]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h2140, h2527, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h0, h2140, h2459, hc01, hc23, hlam, hphi, ht12, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h1673, h2528, h2557, hc01, hc23, hlam, hphi, ht12, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h0, h1673, h2528, h2557, hc01, hc23, hlam, hphi, ht12, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h2525, hlam, p2558_0]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [hlam, p2558_0]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h1673, h2526, h2528, h2557, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2558_1, u3ehi4]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h0, h2459, hc01, hc25, hlam, hphi, ht12, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h2526, hlam, p2558_0]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [h2527, hlam, p2558_1]
                · have p2558_0 := h2558c.1
                  have p2558_1 := h2558c.2.1
                  have p2558_2 := h2558c.2.2.1
                  have p2558_3 := h2558c.2.2.2
                  linarith only [hlam, p2558_0]
              · linarith only [h0, h1337, h2140, h2525, h2557, hc01, hc13, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2585 | h2585
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2586 | h2586
              · rcases h0bigk with h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [hlam, p2587_0]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h0, hlam, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h1337, hlam, p2587_0]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h1673, hlam, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h1959, hlam, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [hlam, p2587_0]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h2140, hlam, p2587_0]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h2356, hlam, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h2459, hlam, p2587_0]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h2140, hc01, hc23, hlam, hphi, ht12, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h2140, hc02, hc23, hlam, hphi, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [hlam, p2587_0]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h2140, h2525, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2587_1, u3ehi3]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h1959, h2140, hc01, hc23, hlam, hphi, ht12, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h1673, hc01, hc14, hlam, hphi, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h0, h2356, hc01, hc24, hlam, hphi, ht12, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h2525, hlam, p2587_0]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [hlam, p2587_0]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h2527, hlam, p2587_0]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h0, h2459, hc01, hc25, hlam, hphi, ht12, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h2526, hlam, p2587_0]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [h2527, hc04, hc45, hlam, hphi, p2587_1]
                · have p2587_0 := h2587c.1
                  have p2587_1 := h2587c.2.1
                  have p2587_2 := h2587c.2.2.1
                  have p2587_3 := h2587c.2.2.2
                  linarith only [hlam, p2587_0]
              · linarith only [h0, h2140, h2356, h2525, h2585, h2586, hc01, hc12, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2614 | h2614
              · rcases h0bigk with h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [hlam, p2615_0]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h0, hlam, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h1337, hlam, p2615_0]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h1673, hlam, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h1959, hlam, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [hlam, p2615_0]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h2140, hlam, p2615_0]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h2356, hlam, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h2459, hlam, p2615_0]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h2140, hc01, hc23, hlam, hphi, ht12, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h2140, hc02, hc23, hlam, hphi, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [hlam, p2615_0]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h2140, h2525, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2615_1, u3ehi3]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h1959, h2140, hc01, hc23, hlam, hphi, ht12, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h1673, hc01, hc14, hlam, hphi, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h0, h2356, hc01, hc24, hlam, hphi, ht12, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h2525, hlam, p2615_0]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [hlam, p2615_0]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h2527, hlam, p2615_0]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h0, h2459, hc01, hc25, hlam, hphi, ht12, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h2526, hlam, p2615_0]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [h2527, hc04, hc45, hlam, hphi, p2615_1]
                · have p2615_0 := h2615c.1
                  have p2615_1 := h2615c.2.1
                  have p2615_2 := h2615c.2.2.1
                  have p2615_3 := h2615c.2.2.2
                  linarith only [hlam, p2615_0]
              · linarith only [h0, h1337, h2140, h2525, h2614, hc01, hc13, hlam, hphi]
        · linarith only [h2525, h2526, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2643 | h2643
        · linarith only [h2525, h2643, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2645 | h2645
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2646 | h2646
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2647 | h2647
              · rcases h0bigk with h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [hlam, p2648_0]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h0, hlam, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h1337, hlam, p2648_0]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h1673, hlam, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h1959, hlam, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [hlam, p2648_0]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2140, hlam, p2648_0]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2356, hlam, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2459, hlam, p2648_0]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2525, h2647, hc01, hc23, hlam, hphi, ht12, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2525, h2647, hc02, hc23, hlam, hphi, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [hlam, p2648_0]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2525, hlam, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2643, hlam, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2525, h2647, hc01, hc23, hlam, hphi, ht12, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h0, h2525, h2647, hc01, hc23, hlam, hphi, ht12, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2525, h2647, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2648_1, u3ehi0]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [hlam, p2648_0]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2525, h2647, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h0, h2459, hc01, hc25, hlam, hphi, ht12, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2643, hc35, hlam, hphi, p2648_1, u3ehi0]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [h2645, hlam, p2648_1]
                · have p2648_0 := h2648c.1
                  have p2648_1 := h2648c.2.1
                  have p2648_2 := h2648c.2.2.1
                  have p2648_3 := h2648c.2.2.2
                  linarith only [hlam, p2648_0]
              · rcases h0bigk with h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [hlam, p2674_0]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h0, hlam, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h1337, hlam, p2674_0]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h1673, hlam, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h1959, hlam, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2140, hc01, hc23, hlam, hphi, ht12, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [hlam, p2674_0]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2140, hlam, p2674_0]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2356, hlam, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2459, hlam, p2674_0]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2140, h2647, hc02, hc34, hlam, hphi, ht23, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [hlam, p2674_0]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2525, hlam, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2643, hlam, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2356, h2646, hc01, hc12, hlam, hphi, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h0, h2356, h2646, hc01, hc12, hlam, hphi, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2356, h2646, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2674_1, u3ehi0]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [hlam, p2674_0]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2356, h2646, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h0, h2459, hc01, hc25, hlam, hphi, ht12, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2643, hc35, hlam, hphi, p2674_1, u3ehi0]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [h2645, hlam, p2674_1]
                · have p2674_0 := h2674c.1
                  have p2674_1 := h2674c.2.1
                  have p2674_2 := h2674c.2.2.1
                  have p2674_3 := h2674c.2.2.2
                  linarith only [hlam, p2674_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2700 | h2700
              · rcases h0bigk with h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [hlam, p2701_0]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h0, hlam, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h1337, hlam, p2701_0]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h1673, hlam, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h1959, hlam, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [hlam, p2701_0]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h2140, hlam, p2701_0]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h2356, hlam, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h2459, hlam, p2701_0]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h2140, hc02, hc23, hlam, hphi, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [hlam, p2701_0]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h2525, hlam, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h2643, hlam, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h2525, h2700, hc01, hc23, hlam, hphi, ht12, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h0, h2525, h2700, hc01, hc23, hlam, hphi, ht12, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h2525, h2700, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2701_1, u3ehi0]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [hlam, p2701_0]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h2525, h2700, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h0, h2459, hc01, hc25, hlam, hphi, ht12, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h2643, hc35, hlam, hphi, p2701_1, u3ehi0]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [h2645, hlam, p2701_1]
                · have p2701_0 := h2701c.1
                  have p2701_1 := h2701c.2.1
                  have p2701_2 := h2701c.2.2.1
                  have p2701_3 := h2701c.2.2.2
                  linarith only [hlam, p2701_0]
              · rcases h0bigk with h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c | h2727c
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [hlam, p2727_0]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h0, hlam, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h1337, hlam, p2727_0]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h1673, hlam, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h1959, hlam, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h0, h2646, h2700, hc01, hc34, hlam, hphi, ht12, ht23, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [hlam, p2727_0]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h2140, hlam, p2727_0]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h2356, hlam, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h2459, hlam, p2727_0]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h2140, h2700, hc02, hc34, hlam, hphi, ht23, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [hlam, p2727_0]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h2525, hlam, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h2643, hlam, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h1673, h2646, h2700, hc01, hc34, hlam, hphi, ht12, ht23, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h0, h1673, h2646, h2700, hc01, hc34, hlam, hphi, ht12, ht23, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h1673, h2646, h2700, hc34, hlam, hphi, p2727_1, u3ehi0]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [hlam, p2727_0]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h1673, h1959, h2646, h2700, hc01, hc34, hlam, hphi, ht12, ht23, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h1959, hc01, hc15, hlam, hphi, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h0, h2459, hc01, hc25, hlam, hphi, ht12, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h2643, hc35, hlam, hphi, p2727_1, u3ehi0]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [h2645, hlam, p2727_1]
                · have p2727_0 := h2727c.1
                  have p2727_1 := h2727c.2.1
                  have p2727_2 := h2727c.2.2.1
                  have p2727_3 := h2727c.2.2.2
                  linarith only [hlam, p2727_0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2753 | h2753
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2754 | h2754
              · rcases h0bigk with h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [hlam, p2755_0]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h0, hlam, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h1337, hlam, p2755_0]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h1673, hlam, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h1959, hlam, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [hlam, p2755_0]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2140, hlam, p2755_0]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2356, hlam, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2459, hlam, p2755_0]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2525, h2754, hc01, hc24, hlam, hphi, ht12, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2525, h2754, hc02, hc24, hlam, hphi, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [hlam, p2755_0]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2525, hlam, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2643, hlam, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h0, h2645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2645, hc45, hlam, hphi, ht34, p2755_1, u3ehi0]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [hlam, p2755_0]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2645, hlam, p2755_0]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h0, h2645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2645, hc45, hlam, hphi, ht34, p2755_1, u3ehi0]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [h2645, hc04, hc45, hlam, hphi, p2755_1]
                · have p2755_0 := h2755c.1
                  have p2755_1 := h2755c.2.1
                  have p2755_2 := h2755c.2.2.1
                  have p2755_3 := h2755c.2.2.2
                  linarith only [hlam, p2755_0]
              · rcases h0bigk with h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c | h2781c
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [hlam, p2781_0]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h0, hlam, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h1337, hlam, p2781_0]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h1673, hlam, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h1959, hlam, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [hlam, p2781_0]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h2140, hlam, p2781_0]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h2356, hlam, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h2459, hlam, p2781_0]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h2140, h2754, hc02, hc34, hlam, hphi, ht23, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [hlam, p2781_0]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h2525, hlam, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h2643, hlam, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h1673, h2753, hc01, hc12, hlam, hphi, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h0, h2356, h2753, hc01, hc12, hlam, hphi, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h2356, h2753, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2781_1, u3ehi0]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [hlam, p2781_0]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h2645, hlam, p2781_0]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h2645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h0, h2645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h2645, hc45, hlam, hphi, ht34, p2781_1, u3ehi0]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [h2645, hc04, hc45, hlam, hphi, p2781_1]
                · have p2781_0 := h2781c.1
                  have p2781_1 := h2781c.2.1
                  have p2781_2 := h2781c.2.2.1
                  have p2781_3 := h2781c.2.2.2
                  linarith only [hlam, p2781_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2807 | h2807
              · rcases h0bigk with h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c | h2808c
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [hlam, p2808_0]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h0, hlam, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h1337, hlam, p2808_0]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h1673, hlam, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h1959, hlam, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [hlam, p2808_0]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h2140, hlam, p2808_0]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h2356, hlam, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h2459, hlam, p2808_0]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h1673, h2525, h2753, h2807, hc02, hc23, hlam, hphi, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [hlam, p2808_0]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h2525, hlam, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h2643, hlam, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h1673, h2753, h2807, hc01, hc23, hlam, hphi, ht12, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h0, h1673, h2753, h2807, hc01, hc23, hlam, hphi, ht12, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h1673, h2753, h2807, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2808_1, u3ehi0]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [hlam, p2808_0]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h2645, hlam, p2808_0]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h2645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h0, h2645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h2645, hc45, hlam, hphi, ht34, p2808_1, u3ehi0]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [h2645, hc04, hc45, hlam, hphi, p2808_1]
                · have p2808_0 := h2808c.1
                  have p2808_1 := h2808c.2.1
                  have p2808_2 := h2808c.2.2.1
                  have p2808_3 := h2808c.2.2.2
                  linarith only [hlam, p2808_0]
              · rcases h0bigk with h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [hlam, p2834_0]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h0, hlam, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h1337, hlam, p2834_0]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h1673, hlam, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h1959, hlam, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h2140, hc01, hc23, hlam, hphi, ht12, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [hlam, p2834_0]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h2140, hlam, p2834_0]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h2356, hlam, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h2459, hlam, p2834_0]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h1337, hc01, hc13, hlam, hphi, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h1673, h2525, h2753, h2807, hc02, hc34, hlam, hphi, ht23, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [hlam, p2834_0]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h2525, hlam, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h2643, hlam, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h1673, h2753, h2807, hc01, hc34, hlam, hphi, ht12, ht23, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h0, h1673, h2753, h2807, hc01, hc34, hlam, hphi, ht12, ht23, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h1673, h2753, h2807, hc34, hlam, hphi, p2834_1, u3ehi0]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [hlam, p2834_0]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h2645, hlam, p2834_0]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h2645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h0, h2645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h2645, hc45, hlam, hphi, ht34, p2834_1, u3ehi0]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [h2645, hc04, hc45, hlam, hphi, p2834_1]
                · have p2834_0 := h2834c.1
                  have p2834_1 := h2834c.2.1
                  have p2834_2 := h2834c.2.2.1
                  have p2834_3 := h2834c.2.2.2
                  linarith only [hlam, p2834_0]

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1337 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1673 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1959 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h2140 | h2140
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h1337 h1673 h1959 h2140
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h1337 h1673 h1959 h2140

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1337 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1673 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h1959 | h1959
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h1337 h1673 h1959
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h1337 h1673 h1959

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1337 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h1673 | h1673
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h1337 h1673
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h1337 h1673

end R2N4
