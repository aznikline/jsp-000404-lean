import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8436000 in
set_option maxHeartbeats 8436000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2564 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2565 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2566 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h3389 | h3389
  · rcases m.htr 1 3 5 (by decide) (by decide) with h3390 | h3390
    · linarith only [h2564, h2566, h3390, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h3392 | h3392
      · linarith only [h2, h3389, h3390, h3392, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3394 | h3394
        · linarith only [h0, h2564, h2566, h3394, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h2564, h2566, h3389, h3394, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h3397 | h3397
    · linarith only [h2564, h2566, h3389, h3397, h7, h9, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h3399 | h3399
      · linarith only [h0, h2565, h3389, h3399, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3401 | h3401
        · linarith only [h2564, h3389, h3401, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h3403 | h3403
          · linarith only [h0, h2564, h2566, h3397, h3403, h6, hc01, hc15, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h3405 | h3405
            · linarith only [h2565, h3389, h3405, h7, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3407 | h3407
              · linarith only [h2565, h2566, h3403, h3407, h7, h8, h9, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h0bigk with h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c | h3409c
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [hlam, p3409_0]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h2565, h2566, h3401, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3409_1]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h2565, h2566, h3401, h3403, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3409_1]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  rcases p3409_3 (m.d 0 1) (by simp) with h3413 | h3413
                  · rcases p3409_3 (m.d 0 2) (by simp) with h3414 | h3414
                    · linarith only [h0, h3414, hlam]
                    · linarith only [h3414, h5, hlam]
                  · linarith only [h2, h3413, hlam]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h2565, h2566, h3401, h3403, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3409_1]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h0, hlam, p3409_0]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [hlam, p3409_0]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h2565, h2566, h3401, h3403, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3409_1]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  rcases p3409_3 (m.d 0 1) (by simp) with h3422 | h3422
                  · rcases p3409_3 (m.d 0 2) (by simp) with h3423 | h3423
                    · rcases p3409_3 (m.d 0 3) (by simp) with h3424 | h3424
                      · linarith only [h3424, h4, hlam]
                      · linarith only [h3424, h7, hlam]
                    · linarith only [h3423, h5, hlam]
                  · linarith only [h2, h3422, hlam]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h0, h2565, h2566, h3401, h3403, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3409_1]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h1, hlam, p3409_1]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h4, hlam, p3409_1]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [hlam, p3409_0]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  rcases p3409_3 (m.d 0 1) (by simp) with h3433 | h3433
                  · rcases p3409_3 (m.d 0 2) (by simp) with h3434 | h3434
                    · rcases p3409_3 (m.d 0 3) (by simp) with h3435 | h3435
                      · rcases p3409_3 (m.d 0 4) (by simp) with h3436 | h3436
                        · linarith only [h3436, h7, hlam]
                        · rcases p3409_3 (m.d 0 5) (by simp) with h3438 | h3438
                          · linarith only [h3438, h8, hlam]
                          · linarith only [h3438, h9, hlam]
                      · linarith only [h3435, h7, hlam]
                    · linarith only [h3434, h5, hlam]
                  · linarith only [h2, h3433, hlam]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h0, h2565, h2566, h3401, h3403, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3409_1]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h2, hlam, p3409_0]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h5, hlam, p3409_0]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h7, hlam, p3409_0]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [hlam, p3409_0]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h9, hlam, p3409_0]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h3, hlam, p3409_0]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h6, hlam, p3409_1]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h8, hlam, p3409_0]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [h2564, h3389, h7, h9, hc23, hc45, hlam, hphi, ht34, p3409_1]
                · have p3409_0 := h3409c.1
                  have p3409_1 := h3409c.2.1
                  have p3409_2 := h3409c.2.2.1
                  have p3409_3 := h3409c.2.2.2
                  linarith only [hlam, p3409_0]

set_option maxHeartbeats 8436000 in
set_option maxHeartbeats 8436000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2564 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2565 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h2566 | h2566
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2564 h2565 h2566
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2564 h2565 h2566

set_option maxHeartbeats 8436000 in
set_option maxHeartbeats 8436000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2564 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2565 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  linarith only [h2564, h2565, h5, h9, hc23, hc45, hlam, hphi, ht34]

set_option maxHeartbeats 8436000 in
set_option maxHeartbeats 8436000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2564 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h2565 | h2565
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2564 h2565
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2564 h2565

end R2N4
