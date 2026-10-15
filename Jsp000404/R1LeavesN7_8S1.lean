import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 4 (by decide) (by decide) with h439 | h439
  · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
    · linarith only [h0, h10, h4, h440, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h442 | h442
      · rcases m.htr 1 3 5 (by decide) (by decide) with h443 | h443
        · rcases m.htr 1 4 5 (by decide) (by decide) with h444 | h444
          · linarith only [h0, h10, h4, h439, h444, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
            · rcases m.htr 2 3 5 (by decide) (by decide) with h447 | h447
              · rcases m.htr 2 4 5 (by decide) (by decide) with h448 | h448
                · linarith only [h0, h4, h439, h440, h444, h447, h448, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h450 | h450
                  · linarith only [h439, h440, h446, h448, h450, hlam]
                  · rcases h0bigk with h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h4, h440, h448, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h439, h440, h446, h448, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h439, h440, h446, h448, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h439, h440, h446, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h0, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h439, h440, h446, h448, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h0, h439, h440, h446, h448, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h0, h439, h440, h446, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h1, hlam, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h4, hlam, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h439, h440, h446, h448, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h0, h4, h439, h440, h446, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h2, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h5, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h7, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h439, h440, h446, h6, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h3, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h6, hlam, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h8, hlam, p452_0]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [h9, hlam, p452_1]
                    · have p452_0 := h452c.1
                      have p452_1 := h452c.2.1
                      have p452_2 := h452c.2.2.1
                      have p452_3 := h452c.2.2.2
                      linarith only [hlam, p452_0]
              · linarith only [h10, h439, h443, h446, h447, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h439, h446, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h480 | h480
          · linarith only [h0, h10, h4, h439, h480, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h482 | h482
            · rcases m.htr 2 3 5 (by decide) (by decide) with h483 | h483
              · linarith only [h0, h10, h4, h439, h443, h482, h483, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10, h4, h439, h482, h483, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h439, h482, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h439, h442, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h488 | h488
    · linarith only [h0, h439, h488, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h490 | h490
      · rcases m.htr 1 3 5 (by decide) (by decide) with h491 | h491
        · rcases m.htr 1 4 5 (by decide) (by decide) with h492 | h492
          · rcases m.htr 2 3 4 (by decide) (by decide) with h493 | h493
            · rcases m.htr 2 3 5 (by decide) (by decide) with h494 | h494
              · rcases m.htr 2 4 5 (by decide) (by decide) with h495 | h495
                · rcases m.htr 3 4 5 (by decide) (by decide) with h496 | h496
                  · linarith only [h1, h490, h496, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases h0bigk with h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [hlam, p498_0]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h4, h488, h493, h495, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p498_1]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h2, h492, h496, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p498_1]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h2, h492, h496, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p498_1]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      rcases p498_3 (m.d 0 1) (by simp) with h503 | h503
                      · rcases p498_3 (m.d 0 2) (by simp) with h504 | h504
                        · linarith only [h0, h504, hlam]
                        · linarith only [h504, h6, hlam]
                      · linarith only [h3, h503, hlam]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h0, hlam, p498_0]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [hlam, p498_0]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h4, h439, h492, h493, h496, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p498_1]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h0, h439, h492, h496, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p498_1]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      rcases p498_3 (m.d 0 1) (by simp) with h512 | h512
                      · rcases p498_3 (m.d 0 2) (by simp) with h513 | h513
                        · rcases p498_3 (m.d 0 3) (by simp) with h514 | h514
                          · linarith only [h4, h514, hlam]
                          · linarith only [h514, h8, hlam]
                        · linarith only [h513, h6, hlam]
                      · linarith only [h3, h512, hlam]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h1, hlam, p498_1]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h4, hlam, p498_1]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [hlam, p498_0]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h439, h492, h496, h5, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p498_1]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      rcases p498_3 (m.d 0 1) (by simp) with h523 | h523
                      · rcases p498_3 (m.d 0 2) (by simp) with h524 | h524
                        · rcases p498_3 (m.d 0 3) (by simp) with h525 | h525
                          · rcases p498_3 (m.d 0 4) (by simp) with h526 | h526
                            · linarith only [h526, h7, hlam]
                            · linarith only [h526, h9, hlam]
                          · linarith only [h525, h8, hlam]
                        · linarith only [h524, h6, hlam]
                      · linarith only [h3, h523, hlam]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h2, hlam, p498_0]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h5, hlam, p498_0]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h7, hlam, p498_0]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [hlam, p498_0]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      rcases p498_3 (m.d 0 1) (by simp) with h536 | h536
                      · rcases p498_3 (m.d 0 2) (by simp) with h537 | h537
                        · rcases p498_3 (m.d 0 3) (by simp) with h538 | h538
                          · rcases p498_3 (m.d 0 4) (by simp) with h539 | h539
                            · rcases p498_3 (m.d 0 5) (by simp) with h540 | h540
                              · linarith only [h540, h9, hlam]
                              · rcases h2bigk with h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h488, h5, h6, hlam, p498_1, p542_2]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h439, h492, h493, h496, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h0, h439, h492, h496, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  rcases p542_3 (m.d 0 2) (by simp) with h547 | h547
                                  · rcases p542_3 (m.d 1 2) (by simp) with h548 | h548
                                    · linarith only [h0, h548, hlam]
                                    · rcases p542_3 (m.d 2 3) (by simp) with h550 | h550
                                      · linarith only [h4, h550, hlam]
                                      · linarith only [h494, h550, hlam]
                                  · linarith only [h547, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h0, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h10, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h439, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h488, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h4, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  rcases p542_3 (m.d 0 2) (by simp) with h560 | h560
                                  · rcases p542_3 (m.d 1 2) (by simp) with h561 | h561
                                    · linarith only [h561, hlam, p542_0]
                                    · rcases p542_3 (m.d 2 3) (by simp) with h563 | h563
                                      · rcases p542_3 (m.d 2 4) (by simp) with h564 | h564
                                        · linarith only [h493, h564, hlam]
                                        · linarith only [h439, h564, hlam]
                                      · linarith only [h563, hlam, p542_0]
                                  · linarith only [h0, h560, hlam]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h439, h492, h496, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h0, h4, h488, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h5, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  rcases p542_3 (m.d 0 2) (by simp) with h573 | h573
                                  · rcases p542_3 (m.d 1 2) (by simp) with h574 | h574
                                    · linarith only [h574, hlam, p542_0]
                                    · rcases p542_3 (m.d 2 3) (by simp) with h576 | h576
                                      · rcases p542_3 (m.d 2 4) (by simp) with h577 | h577
                                        · rcases p542_3 (m.d 2 5) (by simp) with h578 | h578
                                          · linarith only [h495, h578, hlam]
                                          · linarith only [h488, h578, hlam]
                                        · linarith only [h577, hlam, p542_0]
                                      · linarith only [h10, h576, hlam]
                                  · linarith only [h0, h573, hlam]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h493, hlam, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h488, hc12, hc24, hlam, hphi, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h6, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h0, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p498_1, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h494, hlam, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h495, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [hlam, p542_0]
                            · linarith only [h539, h9, hlam]
                          · linarith only [h538, h8, hlam]
                        · linarith only [h537, h6, hlam]
                      · linarith only [h3, h536, hlam]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h3, hlam, p498_0]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h6, hlam, p498_1]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h8, hlam, p498_0]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [h9, hlam, p498_1]
                    · have p498_0 := h498c.1
                      have p498_1 := h498c.2.1
                      have p498_2 := h498c.2.2.1
                      have p498_3 := h498c.2.2.2
                      linarith only [hlam, p498_0]
                · linarith only [h2, h439, h492, h495, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h10, h4, h490, h492, h494, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · linarith only [h0, h10, h4, h490, h492, h493, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
            · rcases m.htr 2 3 5 (by decide) (by decide) with h605 | h605
              · rcases m.htr 2 4 5 (by decide) (by decide) with h606 | h606
                · rcases m.htr 3 4 5 (by decide) (by decide) with h607 | h607
                  · linarith only [h490, h492, h607, hlam]
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
                      linarith only [h4, h492, h604, h606, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h1, h491, hc01, hlam, hphi, ht0b, ht5b, p609_1, u5ehi3]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h490, h492, h5, h606, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      rcases p609_3 (m.d 0 1) (by simp) with h614 | h614
                      · rcases p609_3 (m.d 0 2) (by simp) with h615 | h615
                        · linarith only [h0, h615, hlam]
                        · linarith only [h6, h615, hlam]
                      · linarith only [h3, h614, hlam]
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
                      linarith only [h4, h439, h492, h604, h606, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h0, h439, h492, h5, h606, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      rcases p609_3 (m.d 0 1) (by simp) with h623 | h623
                      · rcases p609_3 (m.d 0 2) (by simp) with h624 | h624
                        · rcases p609_3 (m.d 0 3) (by simp) with h625 | h625
                          · linarith only [h4, h625, hlam]
                          · linarith only [h625, h8, hlam]
                        · linarith only [h6, h624, hlam]
                      · linarith only [h3, h623, hlam]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h1, hlam, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h4, hlam, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h439, h492, h5, h606, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      rcases p609_3 (m.d 0 1) (by simp) with h634 | h634
                      · rcases p609_3 (m.d 0 2) (by simp) with h635 | h635
                        · rcases p609_3 (m.d 0 3) (by simp) with h636 | h636
                          · rcases p609_3 (m.d 0 4) (by simp) with h637 | h637
                            · linarith only [h637, h7, hlam]
                            · linarith only [h637, h9, hlam]
                          · linarith only [h636, h8, hlam]
                        · linarith only [h6, h635, hlam]
                      · linarith only [h3, h634, hlam]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h2, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h5, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h7, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      rcases p609_3 (m.d 0 1) (by simp) with h647 | h647
                      · rcases p609_3 (m.d 0 2) (by simp) with h648 | h648
                        · rcases p609_3 (m.d 0 3) (by simp) with h649 | h649
                          · rcases p609_3 (m.d 0 4) (by simp) with h650 | h650
                            · rcases p609_3 (m.d 0 5) (by simp) with h651 | h651
                              · linarith only [h651, h9, hlam]
                              · rcases h2bigk with h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h4, h439, h492, h604, h606, hlam, p653_2]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h0, h439, h492, h604, h606, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p653_1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h0, h439, h492, h606, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p653_1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  rcases p653_3 (m.d 0 2) (by simp) with h658 | h658
                                  · rcases p653_3 (m.d 1 2) (by simp) with h659 | h659
                                    · linarith only [h0, h659, hlam]
                                    · rcases p653_3 (m.d 2 3) (by simp) with h661 | h661
                                      · linarith only [h4, h661, hlam]
                                      · linarith only [h605, h661, hlam]
                                  · linarith only [h658, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h0, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h10, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h439, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h488, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h4, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  rcases p653_3 (m.d 0 2) (by simp) with h671 | h671
                                  · rcases p653_3 (m.d 1 2) (by simp) with h672 | h672
                                    · linarith only [h672, hlam, p653_0]
                                    · rcases p653_3 (m.d 2 3) (by simp) with h674 | h674
                                      · rcases p653_3 (m.d 2 4) (by simp) with h675 | h675
                                        · linarith only [h604, h675, hlam]
                                        · linarith only [h439, h675, hlam]
                                      · linarith only [h674, hlam, p653_0]
                                  · linarith only [h0, h671, hlam]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h492, h606, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p653_1, u5ehi1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h0, h4, h439, h492, h606, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p653_1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h5, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  rcases p653_3 (m.d 0 2) (by simp) with h684 | h684
                                  · rcases p653_3 (m.d 1 2) (by simp) with h685 | h685
                                    · linarith only [h685, hlam, p653_0]
                                    · rcases p653_3 (m.d 2 3) (by simp) with h687 | h687
                                      · rcases p653_3 (m.d 2 4) (by simp) with h688 | h688
                                        · rcases p653_3 (m.d 2 5) (by simp) with h689 | h689
                                          · linarith only [h606, h689, hlam]
                                          · linarith only [h488, h689, hlam]
                                        · linarith only [h688, hlam, p653_0]
                                      · linarith only [h10, h687, hlam]
                                  · linarith only [h0, h684, hlam]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h604, hlam, p653_1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h439, h492, h606, hc12, hc24, hlam, hphi, p653_1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h6, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h6, h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p609_1, p653_1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h605, hlam, p653_1]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [h606, hlam, p653_0]
                                · have p653_0 := h653c.1
                                  have p653_1 := h653c.2.1
                                  have p653_2 := h653c.2.2.1
                                  have p653_3 := h653c.2.2.2
                                  linarith only [hlam, p653_0]
                            · linarith only [h650, h9, hlam]
                          · linarith only [h649, h8, hlam]
                        · linarith only [h6, h648, hlam]
                      · linarith only [h3, h647, hlam]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h3, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h6, hlam, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h8, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h9, hlam, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [hlam, p609_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h712 | h712
                  · linarith only [h0, h10, h4, h488, h490, h606, h712, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                  · rcases h0bigk with h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [hlam, p714_0]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h10, h4, h491, hc01, hlam, hphi, ht0b, ht5b, p714_1, u5ehi3]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h1, h491, hc01, hlam, hphi, ht0b, ht5b, p714_1, u5ehi3]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h439, h606, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h439, h606, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h0, hlam, p714_0]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [hlam, p714_0]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h439, h606, h8, h9, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h0, h439, h606, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h0, h439, h606, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h1, hlam, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h4, hlam, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [hlam, p714_0]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h0, h4, h439, h606, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h0, h4, h439, h606, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h2, hlam, p714_0]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h5, hlam, p714_0]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h7, hlam, p714_0]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [hlam, p714_0]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h439, h606, h9, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h3, hlam, p714_0]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h6, hlam, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h8, hlam, p714_0]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [h9, hlam, p714_1]
                    · have p714_0 := h714c.1
                      have p714_1 := h714c.2.1
                      have p714_2 := h714c.2.2.1
                      have p714_3 := h714c.2.2.2
                      linarith only [hlam, p714_0]
              · linarith only [h10, h491, h605, hlam]
            · linarith only [h10, h490, h491, h492, h604, h9, hc05, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h742 | h742
          · linarith only [h0, h4, h490, h491, h742, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h744 | h744
            · rcases m.htr 2 3 5 (by decide) (by decide) with h745 | h745
              · linarith only [h0, h4, h490, h491, h745, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h747 | h747
                · linarith only [h0, h4, h742, h744, h745, h747, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h749 | h749
                  · linarith only [h1, h490, h747, h749, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [hlam, p751_0]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h10, h4, h7, h745, h749, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h10, h490, h7, h745, h749, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h10, h490, h745, h749, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h10, h490, h745, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h0, hlam, p751_0]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [hlam, p751_0]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h10, h490, h7, h745, h749, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h0, h10, h490, h745, h749, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h0, h10, h490, h745, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h1, hlam, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h4, hlam, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [hlam, p751_0]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h10, h490, h745, h749, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h0, h10, h4, h490, h745, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h2, hlam, p751_0]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h5, hlam, p751_0]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h7, hlam, p751_0]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [hlam, p751_0]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h10, h490, h745, h8, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h3, hlam, p751_0]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h6, hlam, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h8, hlam, p751_0]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [h9, hlam, p751_1]
                    · have p751_0 := h751c.1
                      have p751_1 := h751c.2.1
                      have p751_2 := h751c.2.2.1
                      have p751_3 := h751c.2.2.2
                      linarith only [hlam, p751_0]
            · linarith only [h1, h10, h490, h744, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h778 | h778
        · linarith only [h0, h4, h490, h7, h778, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h780 | h780
          · rcases m.htr 2 3 4 (by decide) (by decide) with h781 | h781
            · linarith only [h0, h4, h490, h780, h781, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h783 | h783
              · linarith only [h0, h4, h7, h781, h783, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h785 | h785
                · rcases m.htr 3 4 5 (by decide) (by decide) with h786 | h786
                  · rcases h0bigk with h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h10, h4, h7, h783, h786, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h10, h7, h783, h786, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h2, h780, hc01, hlam, hphi, ht0b, ht5b, p787_1, u5ehi4]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h10, h783, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h0, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h10, h7, h783, h786, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h0, h10, h7, h783, h786, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h0, h10, h783, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h1, hlam, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h4, hlam, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h10, h7, h783, h786, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h0, h10, h4, h783, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h2, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h5, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h7, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h10, h783, h8, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h3, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h6, hlam, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h8, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h9, hlam, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hlam, p787_0]
                  · linarith only [h10, h2, h490, h780, h786, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h439, h780, h785, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h815 | h815
            · rcases m.htr 2 3 5 (by decide) (by decide) with h816 | h816
              · rcases m.htr 2 4 5 (by decide) (by decide) with h817 | h817
                · rcases m.htr 3 4 5 (by decide) (by decide) with h818 | h818
                  · linarith only [h0, h4, h780, h815, h818, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h10, h4, h490, h815, h817, h818, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h821 | h821
                  · linarith only [h815, h817, h821, hlam]
                  · rcases h0bigk with h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [hlam, p823_0]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h4, h778, h816, hc01, hlam, hphi, ht0b, ht5b, p823_1, u5ehi1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h4, h778, h816, hc01, hlam, hphi, ht0b, ht5b, p823_1, u5ehi1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h10, h490, h815, h817, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h10, h490, h815, h817, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h0, hlam, p823_0]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [hlam, p823_0]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h10, h490, h8, h815, h817, h9, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h0, h10, h490, h815, h817, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h0, h10, h490, h815, h817, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h1, hlam, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h4, hlam, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [hlam, p823_0]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h0, h10, h4, h490, h815, h817, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h0, h10, h4, h490, h815, h817, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h2, hlam, p823_0]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h5, hlam, p823_0]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h7, hlam, p823_0]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [hlam, p823_0]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h10, h490, h815, h817, h9, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h3, hlam, p823_0]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h6, hlam, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h8, hlam, p823_0]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [h9, hlam, p823_1]
                    · have p823_0 := h823c.1
                      have p823_1 := h823c.2.1
                      have p823_2 := h823c.2.2.1
                      have p823_3 := h823c.2.2.2
                      linarith only [hlam, p823_0]
              · linarith only [h10, h490, h815, h816, hc12, hc35, hlam, hphi, ht23]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h850 | h850
              · linarith only [h0, h4, h7, h815, h850, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h852 | h852
                · rcases m.htr 3 4 5 (by decide) (by decide) with h853 | h853
                  · rcases h0bigk with h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [hlam, p854_0]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h4, h7, h850, h853, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h7, h850, h853, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h10, h490, h5, h780, h852, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h10, h8, h850, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h0, hlam, p854_0]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [hlam, p854_0]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h10, h7, h850, h853, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h0, h10, h490, h5, h780, h852, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h0, h10, h8, h850, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h1, hlam, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h4, hlam, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [hlam, p854_0]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h10, h490, h5, h780, h852, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h0, h10, h4, h8, h850, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h2, hlam, p854_0]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h5, hlam, p854_0]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h7, hlam, p854_0]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [hlam, p854_0]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h10, h8, h850, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h3, hlam, p854_0]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h6, hlam, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h8, hlam, p854_0]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [h9, hlam, p854_1]
                    · have p854_0 := h854c.1
                      have p854_1 := h854c.2.1
                      have p854_2 := h854c.2.2.1
                      have p854_3 := h854c.2.2.2
                      linarith only [hlam, p854_0]
                  · linarith only [h815, h852, h853, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h881 | h881
                  · linarith only [h0, h4, h439, h7, h852, h881, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h10, h815, h881, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h10
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h10

end R2N4
