import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 4 5 (by decide) (by decide) with h338 | h338
  · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
    · linarith only [h0, h10, h339, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h341 | h341
      · rcases m.htr 2 4 5 (by decide) (by decide) with h342 | h342
        · rcases m.htr 3 4 5 (by decide) (by decide) with h343 | h343
          · rcases h2bigk with h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h0, h341, h343, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              rcases p344_3 (m.d 0 2) (by simp) with h347 | h347
              · rcases p344_3 (m.d 1 2) (by simp) with h348 | h348
                · linarith only [h0, h348, hlam]
                · linarith only [h348, h7, hlam]
              · linarith only [h347, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              rcases p344_3 (m.d 0 2) (by simp) with h352 | h352
              · rcases p344_3 (m.d 1 2) (by simp) with h353 | h353
                · linarith only [h0, h353, hlam]
                · linarith only [h353, h8, hlam]
              · linarith only [h352, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              rcases p344_3 (m.d 0 2) (by simp) with h357 | h357
              · rcases p344_3 (m.d 1 2) (by simp) with h358 | h358
                · linarith only [h0, h358, hlam]
                · linarith only [h358, h9, hlam]
              · linarith only [h357, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h0, hlam, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h0, h341, h343, hc01, hc45, hlam, hphi, ht0b, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h0, h339, h341, h343, hc01, hc45, hlam, hphi, ht0b, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              rcases p344_3 (m.d 0 2) (by simp) with h366 | h366
              · rcases p344_3 (m.d 1 2) (by simp) with h367 | h367
                · rcases p344_3 (m.d 2 3) (by simp) with h368 | h368
                  · linarith only [h368, h7, hlam]
                  · linarith only [h341, h368, hlam]
                · linarith only [h367, hlam, p344_0]
              · linarith only [h366, h4, hlam]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h2, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h7, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h339, hlam, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h0, h10, h2, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h3, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h8, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h1, h341, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h0, h341, h343, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h4, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h9, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h341, hlam, p344_0]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [h342, hlam, p344_1]
            · have p344_0 := h344c.1
              have p344_1 := h344c.2.1
              have p344_2 := h344c.2.2.1
              have p344_3 := h344c.2.2.2
              linarith only [hlam, p344_0]
          · linarith only [h0, h10, h2, h341, h343, h5, h6, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h10, h2, h338, h339, h341, h342, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h390 | h390
        · rcases m.htr 3 4 5 (by decide) (by decide) with h391 | h391
          · rcases h2bigk with h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h0, h390, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p392_1]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              rcases p392_3 (m.d 0 2) (by simp) with h395 | h395
              · rcases p392_3 (m.d 1 2) (by simp) with h396 | h396
                · linarith only [h0, h396, hlam]
                · linarith only [h396, h7, hlam]
              · linarith only [h395, hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              rcases p392_3 (m.d 0 2) (by simp) with h400 | h400
              · rcases p392_3 (m.d 1 2) (by simp) with h401 | h401
                · linarith only [h0, h401, hlam]
                · linarith only [h401, h8, hlam]
              · linarith only [h400, hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              rcases p392_3 (m.d 0 2) (by simp) with h405 | h405
              · rcases p392_3 (m.d 1 2) (by simp) with h406 | h406
                · linarith only [h0, h406, hlam]
                · linarith only [h406, h9, hlam]
              · linarith only [h405, hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h0, hlam, p392_1]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              rcases p392_3 (m.d 0 2) (by simp) with h412 | h412
              · rcases p392_3 (m.d 1 2) (by simp) with h413 | h413
                · rcases p392_3 (m.d 2 3) (by simp) with h414 | h414
                  · linarith only [h414, hlam, p392_0]
                  · rcases p392_3 (m.d 2 4) (by simp) with h416 | h416
                    · linarith only [h416, h8, hlam]
                    · linarith only [h339, h416, hlam]
                · linarith only [h413, hlam, p392_0]
              · linarith only [h2, h412, hlam]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h0, h390, hc01, hc45, hlam, hphi, ht0b, ht5b, p392_1]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              rcases p392_3 (m.d 0 2) (by simp) with h422 | h422
              · rcases p392_3 (m.d 1 2) (by simp) with h423 | h423
                · rcases p392_3 (m.d 2 3) (by simp) with h424 | h424
                  · linarith only [h424, h7, hlam]
                  · rcases p392_3 (m.d 2 4) (by simp) with h426 | h426
                    · linarith only [h426, h8, hlam]
                    · linarith only [h390, h426, hlam]
                · linarith only [h423, hlam, p392_0]
              · linarith only [h4, h422, hlam]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h2, hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h7, hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h339, hlam, p392_1]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h341, hlam, p392_1]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h3, hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h8, hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p392_1]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h0, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p392_1]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h4, hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h9, hlam, p392_0]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p392_1]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [h390, hlam, p392_1]
            · have p392_0 := h392c.1
              have p392_1 := h392c.2.1
              have p392_2 := h392c.2.2.1
              have p392_3 := h392c.2.2.2
              linarith only [hlam, p392_0]
          · linarith only [h10, h338, h391, hlam]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h447 | h447
          · rcases h2bigk with h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h0, h338, h339, h390, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p448_1]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h10, h2, h338, h339, h390, h5, hlam, p448_2]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h10, h2, h338, h390, h5, hlam, p448_2]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              rcases p448_3 (m.d 0 2) (by simp) with h453 | h453
              · rcases p448_3 (m.d 1 2) (by simp) with h454 | h454
                · linarith only [h0, h454, hlam]
                · linarith only [h454, h9, hlam]
              · linarith only [h453, hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h0, hlam, p448_1]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              rcases p448_3 (m.d 0 2) (by simp) with h460 | h460
              · rcases p448_3 (m.d 1 2) (by simp) with h461 | h461
                · rcases p448_3 (m.d 2 3) (by simp) with h462 | h462
                  · linarith only [h462, hlam, p448_0]
                  · rcases p448_3 (m.d 2 4) (by simp) with h464 | h464
                    · linarith only [h464, h8, hlam]
                    · linarith only [h339, h464, hlam]
                · linarith only [h461, hlam, p448_0]
              · linarith only [h2, h460, hlam]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              rcases p448_3 (m.d 0 2) (by simp) with h469 | h469
              · rcases p448_3 (m.d 1 2) (by simp) with h470 | h470
                · rcases p448_3 (m.d 2 3) (by simp) with h471 | h471
                  · linarith only [h471, h7, hlam]
                  · rcases p448_3 (m.d 2 4) (by simp) with h473 | h473
                    · linarith only [h473, hlam, p448_0]
                    · rcases p448_3 (m.d 2 5) (by simp) with h475 | h475
                      · linarith only [h475, h9, hlam]
                      · linarith only [h390, h475, hlam]
                · linarith only [h470, hlam, p448_0]
              · linarith only [h3, h469, hlam]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              rcases p448_3 (m.d 0 2) (by simp) with h480 | h480
              · rcases p448_3 (m.d 1 2) (by simp) with h481 | h481
                · rcases p448_3 (m.d 2 3) (by simp) with h482 | h482
                  · linarith only [h482, h7, hlam]
                  · rcases p448_3 (m.d 2 4) (by simp) with h484 | h484
                    · linarith only [h484, h8, hlam]
                    · rcases p448_3 (m.d 2 5) (by simp) with h486 | h486
                      · linarith only [h486, hlam, p448_0]
                      · rcases h4bigk with h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h0, h2, h338, h339, h390, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          rcases p488_3 (m.d 0 4) (by simp) with h491 | h491
                          · rcases p488_3 (m.d 1 4) (by simp) with h492 | h492
                            · linarith only [h1, h492, hlam]
                            · linarith only [h492, h8, hlam]
                          · linarith only [h3, h491, hlam]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h0, h10, h2, h338, h339, h390, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h0, h2, h339, h390, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h1, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h10, h339, hc23, hc34, hlam, hphi, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h10, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h0, h10, h2, h339, h390, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h3, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h8, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h339, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h390, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h5, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h0, h2, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h0, h2, h339, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h0, h2, h339, h390, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h6, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h338, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h338, h339, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h447, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                · linarith only [h481, hlam, p448_0]
              · linarith only [h4, h480, hlam]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h2, hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h7, hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h339, hlam, p448_1]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h341, hlam, p448_1]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h3, hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h8, hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p448_1]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h390, hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h4, hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h9, hlam, p448_0]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p448_1]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [h0, h10, h2, h338, h390, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p448_1]
            · have p448_0 := h448c.1
              have p448_1 := h448c.2.1
              have p448_2 := h448c.2.2.1
              have p448_3 := h448c.2.2.2
              linarith only [hlam, p448_0]
          · linarith only [h10, h338, h447, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h536 | h536
    · linarith only [h0, h10, h536, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h538 | h538
      · rcases m.htr 2 4 5 (by decide) (by decide) with h539 | h539
        · linarith only [h338, h539, h8, hlam]
        · linarith only [h536, h538, h539, hlam]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h542 | h542
        · linarith only [h338, h542, h8, hlam]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h544 | h544
          · rcases h2bigk with h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              rcases p545_3 (m.d 0 2) (by simp) with h547 | h547
              · rcases p545_3 (m.d 1 2) (by simp) with h548 | h548
                · linarith only [h0, h548, hlam]
                · rcases p545_3 (m.d 2 3) (by simp) with h550 | h550
                  · linarith only [h2, h550, hlam]
                  · rcases p545_3 (m.d 2 4) (by simp) with h552 | h552
                    · linarith only [h3, h552, hlam]
                    · rcases p545_3 (m.d 2 5) (by simp) with h554 | h554
                      · linarith only [h4, h554, hlam]
                      · rcases h4bigk with h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          rcases p556_3 (m.d 0 4) (by simp) with h558 | h558
                          · rcases p556_3 (m.d 1 4) (by simp) with h559 | h559
                            · linarith only [h1, h559, hlam]
                            · rcases p556_3 (m.d 2 4) (by simp) with h561 | h561
                              · linarith only [h3, h561, hlam]
                              · rcases p556_3 (m.d 3 4) (by simp) with h563 | h563
                                · linarith only [h5, h563, hlam]
                                · linarith only [h10, h563, hlam]
                          · linarith only [h1, h558, hlam]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          rcases p556_3 (m.d 0 4) (by simp) with h567 | h567
                          · rcases p556_3 (m.d 1 4) (by simp) with h568 | h568
                            · linarith only [h1, h568, hlam]
                            · linarith only [h568, h8, hlam]
                          · linarith only [h3, h567, hlam]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h0, h2, h338, h5, h544, hc01, hc15, hlam, hphi, ht0b, ht5b, p556_1]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h0, h2, h338, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p556_1]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h1, hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h338, h536, h6, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h10, hlam, p556_1]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h338, hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h3, hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h8, hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h536, hlam, p556_1]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h542, hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h5, hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h0, h2, h5, h536, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h0, h2, h5, h536, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h0, h2, h338, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p556_1]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h6, hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h536, h544, h8, hc23, hc35, hlam, hphi, p556_1]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h0, h2, h5, h536, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [h544, hlam, p556_0]
                        · have p556_0 := h556c.1
                          have p556_1 := h556c.2.1
                          have p556_2 := h556c.2.2.1
                          have p556_3 := h556c.2.2.2
                          linarith only [hlam, p556_0]
              · linarith only [h0, h547, hlam]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h2, h338, h5, h536, h544, h8, hlam, p545_2]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h2, h338, h5, h544, h8, hlam, p545_2]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              rcases p545_3 (m.d 0 2) (by simp) with h597 | h597
              · rcases p545_3 (m.d 1 2) (by simp) with h598 | h598
                · linarith only [h0, h598, hlam]
                · linarith only [h598, h9, hlam]
              · linarith only [h597, hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h0, hlam, p545_1]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              rcases p545_3 (m.d 0 2) (by simp) with h604 | h604
              · rcases p545_3 (m.d 1 2) (by simp) with h605 | h605
                · rcases p545_3 (m.d 2 3) (by simp) with h606 | h606
                  · linarith only [h606, hlam, p545_0]
                  · rcases p545_3 (m.d 2 4) (by simp) with h608 | h608
                    · linarith only [h608, h8, hlam]
                    · linarith only [h536, h608, hlam]
                · linarith only [h605, hlam, p545_0]
              · linarith only [h2, h604, hlam]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              rcases p545_3 (m.d 0 2) (by simp) with h613 | h613
              · rcases p545_3 (m.d 1 2) (by simp) with h614 | h614
                · rcases p545_3 (m.d 2 3) (by simp) with h615 | h615
                  · linarith only [h615, h7, hlam]
                  · rcases p545_3 (m.d 2 4) (by simp) with h617 | h617
                    · linarith only [h617, hlam, p545_0]
                    · rcases p545_3 (m.d 2 5) (by simp) with h619 | h619
                      · linarith only [h619, h9, hlam]
                      · linarith only [h542, h619, hlam]
                · linarith only [h614, hlam, p545_0]
              · linarith only [h3, h613, hlam]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              rcases p545_3 (m.d 0 2) (by simp) with h624 | h624
              · rcases p545_3 (m.d 1 2) (by simp) with h625 | h625
                · rcases p545_3 (m.d 2 3) (by simp) with h626 | h626
                  · linarith only [h626, h7, hlam]
                  · rcases p545_3 (m.d 2 4) (by simp) with h628 | h628
                    · linarith only [h628, h8, hlam]
                    · rcases p545_3 (m.d 2 5) (by simp) with h630 | h630
                      · linarith only [h630, hlam, p545_0]
                      · rcases h4bigk with h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          rcases p632_3 (m.d 0 4) (by simp) with h634 | h634
                          · rcases p632_3 (m.d 1 4) (by simp) with h635 | h635
                            · linarith only [h1, h635, hlam]
                            · rcases p632_3 (m.d 2 4) (by simp) with h637 | h637
                              · linarith only [h3, h637, hlam]
                              · rcases p632_3 (m.d 3 4) (by simp) with h639 | h639
                                · linarith only [h5, h639, hlam]
                                · linarith only [h10, h639, hlam]
                          · linarith only [h1, h634, hlam]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          rcases p632_3 (m.d 0 4) (by simp) with h643 | h643
                          · rcases p632_3 (m.d 1 4) (by simp) with h644 | h644
                            · linarith only [h1, h644, hlam]
                            · linarith only [h644, h8, hlam]
                          · linarith only [h3, h643, hlam]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h0, h2, h5, h544, hc01, hc45, hlam, hphi, ht0b, ht5b, p632_1]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h0, h2, h338, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p632_1]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h1, hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h338, h536, hc23, hc45, hlam, hphi, ht34, p632_1]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h10, hlam, p632_1]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h338, hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h3, hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h8, hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h536, hlam, p632_1]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h542, hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h5, hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h0, h2, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p632_1]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h0, h2, h5, h536, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p632_1]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h0, h2, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p632_1]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h6, hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h536, h8, hc23, hc45, hlam, hphi, ht34, p632_1]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h0, h2, h5, h536, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p632_1]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [h544, hlam, p632_0]
                        · have p632_0 := h632c.1
                          have p632_1 := h632c.2.1
                          have p632_2 := h632c.2.2.1
                          have p632_3 := h632c.2.2.2
                          linarith only [hlam, p632_0]
                · linarith only [h625, hlam, p545_0]
              · linarith only [h4, h624, hlam]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h2, hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h7, hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h536, hlam, p545_1]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h538, hlam, p545_1]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h3, hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h8, hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p545_1]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h542, hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h4, hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h9, hlam, p545_0]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p545_1]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [h0, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p545_1]
            · have p545_0 := h545c.1
              have p545_1 := h545c.2.1
              have p545_2 := h545c.2.2.1
              have p545_3 := h545c.2.2.2
              linarith only [hlam, p545_0]
          · rcases h2bigk with h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              rcases p687_3 (m.d 0 2) (by simp) with h689 | h689
              · rcases p687_3 (m.d 1 2) (by simp) with h690 | h690
                · linarith only [h0, h690, hlam]
                · rcases p687_3 (m.d 2 3) (by simp) with h692 | h692
                  · linarith only [h2, h692, hlam]
                  · rcases p687_3 (m.d 2 4) (by simp) with h694 | h694
                    · linarith only [h3, h694, hlam]
                    · rcases p687_3 (m.d 2 5) (by simp) with h696 | h696
                      · linarith only [h4, h696, hlam]
                      · rcases h4bigk with h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          rcases p698_3 (m.d 0 4) (by simp) with h700 | h700
                          · rcases p698_3 (m.d 1 4) (by simp) with h701 | h701
                            · linarith only [h1, h701, hlam]
                            · rcases p698_3 (m.d 2 4) (by simp) with h703 | h703
                              · linarith only [h3, h703, hlam]
                              · rcases p698_3 (m.d 3 4) (by simp) with h705 | h705
                                · linarith only [h5, h705, hlam]
                                · linarith only [h10, h705, hlam]
                          · linarith only [h1, h700, hlam]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          rcases p698_3 (m.d 0 4) (by simp) with h709 | h709
                          · rcases p698_3 (m.d 1 4) (by simp) with h710 | h710
                            · linarith only [h1, h710, hlam]
                            · linarith only [h710, h8, hlam]
                          · linarith only [h3, h709, hlam]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h0, h10, h2, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p698_1]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h0, h2, h338, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p698_1]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h1, hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h338, h536, hc23, hc45, hlam, hphi, ht34, p698_1]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h10, hlam, p698_1]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h338, hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h3, hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h8, hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h536, hlam, p698_1]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h542, hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h5, hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h0, h2, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p698_1]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h0, h2, h5, h536, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p698_1]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h544, hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h6, hlam, p698_0]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h0, h2, h5, h536, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p698_1]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h0, h2, h5, h536, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p698_1]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [h0, h2, h5, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p698_1]
                        · have p698_0 := h698c.1
                          have p698_1 := h698c.2.1
                          have p698_2 := h698c.2.2.1
                          have p698_3 := h698c.2.2.2
                          linarith only [hlam, p698_0]
              · linarith only [h0, h689, hlam]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h10, h2, h5, h544, h6, h7, hlam, p687_2]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              rcases p687_3 (m.d 0 2) (by simp) with h738 | h738
              · rcases p687_3 (m.d 1 2) (by simp) with h739 | h739
                · linarith only [h0, h739, hlam]
                · linarith only [h739, h8, hlam]
              · linarith only [h738, hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              rcases p687_3 (m.d 0 2) (by simp) with h743 | h743
              · rcases p687_3 (m.d 1 2) (by simp) with h744 | h744
                · linarith only [h0, h744, hlam]
                · linarith only [h744, h9, hlam]
              · linarith only [h743, hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h0, hlam, p687_1]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              rcases p687_3 (m.d 0 2) (by simp) with h750 | h750
              · rcases p687_3 (m.d 1 2) (by simp) with h751 | h751
                · rcases p687_3 (m.d 2 3) (by simp) with h752 | h752
                  · linarith only [h752, hlam, p687_0]
                  · rcases p687_3 (m.d 2 4) (by simp) with h754 | h754
                    · linarith only [h754, h8, hlam]
                    · linarith only [h536, h754, hlam]
                · linarith only [h751, hlam, p687_0]
              · linarith only [h2, h750, hlam]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              rcases p687_3 (m.d 0 2) (by simp) with h759 | h759
              · rcases p687_3 (m.d 1 2) (by simp) with h760 | h760
                · rcases p687_3 (m.d 2 3) (by simp) with h761 | h761
                  · linarith only [h7, h761, hlam]
                  · rcases p687_3 (m.d 2 4) (by simp) with h763 | h763
                    · linarith only [h763, hlam, p687_0]
                    · rcases p687_3 (m.d 2 5) (by simp) with h765 | h765
                      · linarith only [h765, h9, hlam]
                      · linarith only [h542, h765, hlam]
                · linarith only [h760, hlam, p687_0]
              · linarith only [h3, h759, hlam]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              rcases p687_3 (m.d 0 2) (by simp) with h770 | h770
              · rcases p687_3 (m.d 1 2) (by simp) with h771 | h771
                · rcases p687_3 (m.d 2 3) (by simp) with h772 | h772
                  · linarith only [h7, h772, hlam]
                  · rcases p687_3 (m.d 2 4) (by simp) with h774 | h774
                    · linarith only [h774, h8, hlam]
                    · rcases p687_3 (m.d 2 5) (by simp) with h776 | h776
                      · linarith only [h776, hlam, p687_0]
                      · rcases h4bigk with h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          rcases p778_3 (m.d 0 4) (by simp) with h780 | h780
                          · rcases p778_3 (m.d 1 4) (by simp) with h781 | h781
                            · linarith only [h1, h781, hlam]
                            · rcases p778_3 (m.d 2 4) (by simp) with h783 | h783
                              · linarith only [h3, h783, hlam]
                              · rcases p778_3 (m.d 3 4) (by simp) with h785 | h785
                                · linarith only [h5, h785, hlam]
                                · linarith only [h10, h785, hlam]
                          · linarith only [h1, h780, hlam]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          rcases p778_3 (m.d 0 4) (by simp) with h789 | h789
                          · rcases p778_3 (m.d 1 4) (by simp) with h790 | h790
                            · linarith only [h1, h790, hlam]
                            · linarith only [h790, h8, hlam]
                          · linarith only [h3, h789, hlam]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h0, h10, h2, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p778_1]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h0, h2, h338, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p778_1]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h1, hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h338, hc24, hc45, hlam, hphi, p778_1]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h10, hlam, p778_1]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h338, hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h3, hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h8, hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h536, hlam, p778_1]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h542, hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h5, hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h0, h2, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p778_1]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h0, h2, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p778_1]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h544, hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h6, hlam, p778_0]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h0, h10, h2, h5, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p778_1]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h0, h2, h5, h536, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p778_1]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [h0, h2, h5, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p778_1]
                        · have p778_0 := h778c.1
                          have p778_1 := h778c.2.1
                          have p778_2 := h778c.2.2.1
                          have p778_3 := h778c.2.2.2
                          linarith only [hlam, p778_0]
                · linarith only [h771, hlam, p687_0]
              · linarith only [h4, h770, hlam]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h2, hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h7, hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h536, hlam, p687_1]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h538, hlam, p687_1]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h3, hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h8, hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p687_1]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h542, hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h4, hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h9, hlam, p687_0]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p687_1]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [h0, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p687_1]
            · have p687_0 := h687c.1
              have p687_1 := h687c.2.1
              have p687_2 := h687c.2.2.1
              have p687_3 := h687c.2.2.2
              linarith only [hlam, p687_0]

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
  · exact r1l7_12_24_L_I_H_I_s5_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h8 h9 h10
  · exact r1l7_12_24_L_I_H_I_s5_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h8 h9 h10

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 3 4 (by decide) (by decide) with h833 | h833
  · rcases m.htr 1 4 5 (by decide) (by decide) with h834 | h834
    · linarith only [h8, h834, h9, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h836 | h836
      · linarith only [h0, h4, h7, h836, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h0, h4, h7, h833, h836, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h839 | h839
    · linarith only [h8, h839, h9, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h841 | h841
      · linarith only [h0, h4, h7, h833, h841, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h843 | h843
        · linarith only [h0, h4, h8, h841, h843, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h845 | h845
          · linarith only [h0, h4, h8, h845, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h847 | h847
            · linarith only [h8, h841, h845, h847, h9, hc23, hc34, hlam, hphi]
            · rcases h2bigk with h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                rcases p849_3 (m.d 0 2) (by simp) with h851 | h851
                · rcases p849_3 (m.d 1 2) (by simp) with h852 | h852
                  · linarith only [h0, h852, hlam]
                  · rcases p849_3 (m.d 2 3) (by simp) with h854 | h854
                    · linarith only [h2, h854, hlam]
                    · rcases p849_3 (m.d 2 4) (by simp) with h856 | h856
                      · linarith only [h3, h856, hlam]
                      · rcases p849_3 (m.d 2 5) (by simp) with h858 | h858
                        · linarith only [h4, h858, hlam]
                        · linarith only [h858, h9, hlam]
                · linarith only [h0, h851, hlam]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h2, h5, h6, h8, h841, h843, h847, h9, hlam, p849_2]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h2, h5, h6, h8, h843, h847, h9, hlam, p849_2]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h0, h8, h841, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h0, hlam, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h5, h6, h843, h847, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h5, h6, h843, h847, h9, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h9, hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h2, hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h7, hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h841, hlam, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h843, hlam, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h3, hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h8, hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h0, h2, h5, h6, h8, h843, h847, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h845, hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h4, hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h0, h2, h5, h6, h7, h843, h847, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                rcases p849_3 (m.d 0 2) (by simp) with h882 | h882
                · rcases p849_3 (m.d 1 2) (by simp) with h883 | h883
                  · linarith only [h883, h9, hlam]
                  · linarith only [h7, h883, hlam]
                · linarith only [h2, h882, hlam]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                rcases p849_3 (m.d 0 2) (by simp) with h887 | h887
                · rcases p849_3 (m.d 1 2) (by simp) with h888 | h888
                  · linarith only [h888, h9, hlam]
                  · linarith only [h8, h888, hlam]
                · linarith only [h3, h887, hlam]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hlam, p849_0]

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_12_24_L_I_H_I_s5_x0_x0_x0_x0 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h8 h9
  · exact r1l7_12_24_L_I_H_I_s5_x0_x0_x0_x1 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h8 h9

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 5 (by decide) (by decide) with h893 | h893
  · rcases m.htr 1 3 4 (by decide) (by decide) with h894 | h894
    · linarith only [h7, h8, h894, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h896 | h896
      · rcases m.htr 2 3 4 (by decide) (by decide) with h897 | h897
        · linarith only [h0, h3, h7, h8, h894, h897, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h899 | h899
          · linarith only [h0, h2, h5, h7, h8, h897, h899, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h901 | h901
            · rcases m.htr 3 4 5 (by decide) (by decide) with h902 | h902
              · rcases h2bigk with h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [hlam, p903_0]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  rcases p903_3 (m.d 0 2) (by simp) with h905 | h905
                  · rcases p903_3 (m.d 1 2) (by simp) with h906 | h906
                    · linarith only [h0, h906, hlam]
                    · rcases p903_3 (m.d 2 3) (by simp) with h908 | h908
                      · linarith only [h2, h908, hlam]
                      · rcases p903_3 (m.d 2 4) (by simp) with h910 | h910
                        · linarith only [h3, h910, hlam]
                        · linarith only [h8, h910, hlam]
                  · linarith only [h0, h905, hlam]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h2, h5, h8, h893, h897, h899, hlam, p903_2]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h0, h8, h893, h899, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p903_1]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h3, h8, h893, hlam, p903_2]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h0, hlam, p903_1]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [hlam, p903_0]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h2, h5, h8, h897, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p903_1]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h8, hlam, p903_0]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h2, h5, h8, h897, hc02, hc25, hlam, hphi, ht0b, ht5b, p903_1]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h2, hlam, p903_0]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h7, hlam, p903_0]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [hlam, p903_0]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h897, hlam, p903_1]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h899, hlam, p903_1]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h3, hlam, p903_0]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h0, h2, h5, h7, h897, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p903_1]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  rcases p903_3 (m.d 0 2) (by simp) with h929 | h929
                  · rcases p903_3 (m.d 1 2) (by simp) with h930 | h930
                    · linarith only [h8, h930, hlam]
                    · linarith only [h7, h930, hlam]
                  · linarith only [h2, h929, hlam]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [hlam, p903_0]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  rcases p903_3 (m.d 0 2) (by simp) with h935 | h935
                  · rcases p903_3 (m.d 1 2) (by simp) with h936 | h936
                    · linarith only [h8, h936, hlam]
                    · linarith only [h893, h936, hlam]
                  · linarith only [h4, h935, hlam]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h4, hlam, p903_0]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h893, hlam, p903_0]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h0, h893, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p903_1]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [h901, hlam, p903_1]
                · have p903_0 := h903c.1
                  have p903_1 := h903c.2.1
                  have p903_2 := h903c.2.2.1
                  have p903_3 := h903c.2.2.2
                  linarith only [hlam, p903_0]
              · linarith only [h0, h2, h5, h6, h8, h893, h897, h902, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h8, h893, h896, h901, hlam]
      · linarith only [h8, h893, h896, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h948 | h948
    · linarith only [h7, h8, h948, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h950 | h950
      · rcases m.htr 2 3 4 (by decide) (by decide) with h951 | h951
        · linarith only [h7, h8, h948, h951, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h953 | h953
          · linarith only [h0, h2, h5, h7, h8, h951, h953, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h955 | h955
            · rcases m.htr 3 4 5 (by decide) (by decide) with h956 | h956
              · rcases h2bigk with h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [hlam, p957_0]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  rcases p957_3 (m.d 0 2) (by simp) with h959 | h959
                  · rcases p957_3 (m.d 1 2) (by simp) with h960 | h960
                    · linarith only [h0, h960, hlam]
                    · rcases p957_3 (m.d 2 3) (by simp) with h962 | h962
                      · linarith only [h2, h962, hlam]
                      · rcases p957_3 (m.d 2 4) (by simp) with h964 | h964
                        · linarith only [h3, h964, hlam]
                        · linarith only [h8, h964, hlam]
                  · linarith only [h0, h959, hlam]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h2, h5, h7, h893, h951, h955, hlam, p957_2]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h0, h7, h893, h955, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p957_1]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h0, h7, h893, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p957_1]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h0, hlam, p957_1]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [hlam, p957_0]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h893, h951, h955, hc23, hc34, hlam, hphi, p957_1]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h8, hlam, p957_0]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h893, hlam, p957_0]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h2, hlam, p957_0]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h7, hlam, p957_0]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [hlam, p957_0]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h951, hlam, p957_1]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h953, hlam, p957_1]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h3, hlam, p957_0]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h0, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p957_1]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  rcases p957_3 (m.d 0 2) (by simp) with h983 | h983
                  · rcases p957_3 (m.d 1 2) (by simp) with h984 | h984
                    · linarith only [h8, h984, hlam]
                    · linarith only [h7, h984, hlam]
                  · linarith only [h2, h983, hlam]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [hlam, p957_0]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h0, h2, h5, h7, h893, h951, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p957_1]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h4, hlam, p957_0]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h7, h953, hc23, hc35, hlam, hphi, p957_1]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  rcases p957_3 (m.d 0 2) (by simp) with h992 | h992
                  · rcases p957_3 (m.d 1 2) (by simp) with h993 | h993
                    · linarith only [h893, h993, hlam]
                    · linarith only [h7, h993, hlam]
                  · linarith only [h2, h992, hlam]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [h955, hlam, p957_1]
                · have p957_0 := h957c.1
                  have p957_1 := h957c.2.1
                  have p957_2 := h957c.2.2.1
                  have p957_3 := h957c.2.2.2
                  linarith only [hlam, p957_0]
              · linarith only [h0, h2, h5, h6, h7, h8, h951, h956, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h7, h8, h950, h955, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1001 | h1001
        · linarith only [h0, h1001, h4, h7, h893, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1003 | h1003
          · linarith only [h0, h1003, h2, h5, h6, h7, h8, h950, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1005 | h1005
            · linarith only [h1001, h1005, h7, h8, h950, hc23, hc34, hlam, hphi]
            · linarith only [h0, h1005, h2, h5, h6, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
  · exact r1l7_12_24_L_I_H_I_s5_x0_x0_x0 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h8
  · exact r1l7_12_24_L_I_H_I_s5_x0_x0_x1 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h8

end R2N4
