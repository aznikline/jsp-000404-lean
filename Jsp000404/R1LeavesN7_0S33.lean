import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S29
import Jsp000404.R1LeavesN7_0S30
import Jsp000404.R1LeavesN7_0S31
import Jsp000404.R1LeavesN7_0S32

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x23 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 5) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 5) ∧ (m.d 1 4) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 4) ≤ z)))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  rcases p17727_3 (m.d 0 1) (by simp) with h18461 | h18461
  · rcases p17727_3 (m.d 1 2) (by simp) with h18462 | h18462
    · rcases p17727_3 (m.d 1 3) (by simp) with h18463 | h18463
      · linarith only [h16974, h18463, hlam]
      · rcases p17727_3 (m.d 1 4) (by simp) with h18465 | h18465
        · linarith only [h16976, h18465, hlam]
        · rcases p17727_3 (m.d 1 5) (by simp) with h18467 | h18467
          · rcases h1emax with h18468 | h18468 | h18468 | h18468 | h18468
            · linarith only [h0, h16971, h18468, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h16970, h16971, h16978, h18468, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17727_1]
            · rcases h2bigk with h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c | h18471c
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h16970, h16971, h16978, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p18471_1]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                rcases p18471_3 (m.d 0 2) (by simp) with h18474 | h18474
                · rcases p18471_3 (m.d 1 2) (by simp) with h18475 | h18475
                  · linarith only [h0, h18475, hlam]
                  · linarith only [h16969, h18475, hlam]
                · linarith only [h18474, hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                rcases p18471_3 (m.d 0 2) (by simp) with h18479 | h18479
                · rcases p18471_3 (m.d 1 2) (by simp) with h18480 | h18480
                  · linarith only [h0, h18480, hlam]
                  · linarith only [h16970, h18480, hlam]
                · linarith only [h18479, hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                rcases p18471_3 (m.d 0 2) (by simp) with h18484 | h18484
                · rcases p18471_3 (m.d 1 2) (by simp) with h18485 | h18485
                  · linarith only [h0, h18485, hlam]
                  · linarith only [h16971, h18485, hlam]
                · linarith only [h18484, hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h0, hlam, p18471_1]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                rcases p18471_3 (m.d 0 2) (by simp) with h18491 | h18491
                · rcases p18471_3 (m.d 1 2) (by simp) with h18492 | h18492
                  · rcases p18471_3 (m.d 2 3) (by simp) with h18493 | h18493
                    · linarith only [h18493, hlam, p18471_0]
                    · rcases p18471_3 (m.d 2 4) (by simp) with h18495 | h18495
                      · linarith only [h16970, h18495, hlam]
                      · linarith only [h16978, h18495, hlam]
                  · linarith only [h18492, hlam, p18471_0]
                · linarith only [h18491, h4, hlam]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                rcases p18471_3 (m.d 0 2) (by simp) with h18500 | h18500
                · rcases p18471_3 (m.d 1 2) (by simp) with h18501 | h18501
                  · rcases p18471_3 (m.d 2 3) (by simp) with h18502 | h18502
                    · linarith only [h16969, h18502, hlam]
                    · rcases p18471_3 (m.d 2 4) (by simp) with h18504 | h18504
                      · linarith only [h18504, hlam, p18471_0]
                      · rcases p18471_3 (m.d 2 5) (by simp) with h18506 | h18506
                        · linarith only [h16971, h18506, hlam]
                        · linarith only [h16982, h18506, hlam]
                  · linarith only [h18501, hlam, p18471_0]
                · linarith only [h18500, h5, hlam]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                rcases p18471_3 (m.d 0 2) (by simp) with h18511 | h18511
                · rcases p18471_3 (m.d 1 2) (by simp) with h18512 | h18512
                  · rcases p18471_3 (m.d 2 3) (by simp) with h18513 | h18513
                    · linarith only [h16969, h18513, hlam]
                    · rcases p18471_3 (m.d 2 4) (by simp) with h18515 | h18515
                      · linarith only [h16970, h18515, hlam]
                      · rcases p18471_3 (m.d 2 5) (by simp) with h18517 | h18517
                        · linarith only [h18517, hlam, p18471_0]
                        · rcases h4bigk with h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c | h18519c
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [hlam, p18519_0]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16970, h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p18519_1]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p18519_1]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h7, hlam, p18519_1]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h14159, hlam, p18519_0]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h2, hlam, p18519_0]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [hlam, p18519_0]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16978, h3, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p18519_1]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16972, hlam, p18519_1]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16976, hlam, p18519_0]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h5, hlam, p18519_0]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16970, hlam, p18519_0]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [hlam, p18519_0]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16978, hlam, p18519_1]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16982, hlam, p18519_0]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16984, hc04, hc45, hlam, hphi, p18519_1]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16984, hc14, hc45, hlam, hphi, p18519_1]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16978, h16984, hc23, hc45, hlam, hphi, ht34, p18519_1]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [hlam, p18519_0]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h16984, hlam, p18519_0]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            rcases p18519_3 (m.d 0 4) (by simp) with h18540 | h18540
                            · linarith only [h18540, hlam, p18519_0]
                            · rcases p18519_3 (m.d 1 4) (by simp) with h18542 | h18542
                              · linarith only [h16976, h18542, hlam]
                              · rcases p18519_3 (m.d 2 4) (by simp) with h18544 | h18544
                                · linarith only [h16982, h18544, hlam]
                                · rcases p18519_3 (m.d 3 4) (by simp) with h18546 | h18546
                                  · linarith only [h16984, h18546, hlam]
                                  · linarith only [h18546, h7, hlam]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            rcases p18519_3 (m.d 0 4) (by simp) with h18549 | h18549
                            · linarith only [h14159, h18549, hlam]
                            · linarith only [h18549, h2, hlam]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            rcases p18519_3 (m.d 0 4) (by simp) with h18552 | h18552
                            · linarith only [h14159, h18552, hlam]
                            · linarith only [h18552, h5, hlam]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [h1, h16969, h7, hc23, hc45, hlam, hphi, ht34, p18519_1]
                          · have p18519_0 := h18519c.1
                            have p18519_1 := h18519c.2.1
                            have p18519_2 := h18519c.2.2.1
                            have p18519_3 := h18519c.2.2.2
                            linarith only [hlam, p18519_0]
                  · linarith only [h18512, hlam, p18471_0]
                · linarith only [h18511, h6, hlam]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h4, hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h16969, hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h16978, hlam, p18471_1]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h16980, hlam, p18471_1]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h5, hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h16970, hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h14159, h16970, h2, hc23, hc45, hlam, hphi, ht34, p18471_1]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h16982, hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h6, hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h16971, hlam, p18471_0]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h0, h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18471_1]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [h0, h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p18471_1]
              · have p18471_0 := h18471c.1
                have p18471_1 := h18471c.2.1
                have p18471_2 := h18471c.2.2.1
                have p18471_3 := h18471c.2.2.2
                linarith only [hlam, p18471_0]
            · rcases h2bigk with h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c | h18574c
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h16971, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p17727_1, p18574_1]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                rcases p18574_3 (m.d 0 2) (by simp) with h18577 | h18577
                · rcases p18574_3 (m.d 1 2) (by simp) with h18578 | h18578
                  · linarith only [h0, h18578, hlam]
                  · linarith only [h16969, h18578, hlam]
                · linarith only [h18577, hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                rcases p18574_3 (m.d 0 2) (by simp) with h18582 | h18582
                · rcases p18574_3 (m.d 1 2) (by simp) with h18583 | h18583
                  · linarith only [h0, h18583, hlam]
                  · linarith only [h16970, h18583, hlam]
                · linarith only [h18582, hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                rcases p18574_3 (m.d 0 2) (by simp) with h18587 | h18587
                · rcases p18574_3 (m.d 1 2) (by simp) with h18588 | h18588
                  · linarith only [h0, h18588, hlam]
                  · linarith only [h16971, h18588, hlam]
                · linarith only [h18587, hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h0, hlam, p18574_1]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                rcases p18574_3 (m.d 0 2) (by simp) with h18594 | h18594
                · rcases p18574_3 (m.d 1 2) (by simp) with h18595 | h18595
                  · rcases p18574_3 (m.d 2 3) (by simp) with h18596 | h18596
                    · linarith only [h18596, hlam, p18574_0]
                    · rcases p18574_3 (m.d 2 4) (by simp) with h18598 | h18598
                      · linarith only [h16970, h18598, hlam]
                      · linarith only [h16978, h18598, hlam]
                  · linarith only [h18595, hlam, p18574_0]
                · linarith only [h18594, h4, hlam]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                rcases p18574_3 (m.d 0 2) (by simp) with h18603 | h18603
                · rcases p18574_3 (m.d 1 2) (by simp) with h18604 | h18604
                  · rcases p18574_3 (m.d 2 3) (by simp) with h18605 | h18605
                    · linarith only [h16969, h18605, hlam]
                    · rcases p18574_3 (m.d 2 4) (by simp) with h18607 | h18607
                      · linarith only [h18607, hlam, p18574_0]
                      · rcases p18574_3 (m.d 2 5) (by simp) with h18609 | h18609
                        · linarith only [h16971, h18609, hlam]
                        · linarith only [h16982, h18609, hlam]
                  · linarith only [h18604, hlam, p18574_0]
                · linarith only [h18603, h5, hlam]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                rcases p18574_3 (m.d 0 2) (by simp) with h18614 | h18614
                · rcases p18574_3 (m.d 1 2) (by simp) with h18615 | h18615
                  · rcases p18574_3 (m.d 2 3) (by simp) with h18616 | h18616
                    · linarith only [h16969, h18616, hlam]
                    · rcases p18574_3 (m.d 2 4) (by simp) with h18618 | h18618
                      · linarith only [h16970, h18618, hlam]
                      · rcases p18574_3 (m.d 2 5) (by simp) with h18620 | h18620
                        · linarith only [h18620, hlam, p18574_0]
                        · rcases h4bigk with h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c | h18622c
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [hlam, p18622_0]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16970, h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p18622_1]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p18622_1]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h7, hlam, p18622_1]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h14159, hlam, p18622_0]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h2, hlam, p18622_0]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [hlam, p18622_0]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16978, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17727_1, p18622_1]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16972, hlam, p18622_1]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16976, hlam, p18622_0]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h5, hlam, p18622_0]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16970, hlam, p18622_0]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [hlam, p18622_0]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16978, hlam, p18622_1]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16982, hlam, p18622_0]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16984, hc04, hc45, hlam, hphi, p18622_1]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16984, hc14, hc45, hlam, hphi, p18622_1]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16978, h16984, hc23, hc45, hlam, hphi, ht34, p18622_1]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [hlam, p18622_0]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h16984, hlam, p18622_0]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            rcases p18622_3 (m.d 0 4) (by simp) with h18643 | h18643
                            · linarith only [h18643, hlam, p18622_0]
                            · rcases p18622_3 (m.d 1 4) (by simp) with h18645 | h18645
                              · linarith only [h16976, h18645, hlam]
                              · rcases p18622_3 (m.d 2 4) (by simp) with h18647 | h18647
                                · linarith only [h16982, h18647, hlam]
                                · rcases p18622_3 (m.d 3 4) (by simp) with h18649 | h18649
                                  · linarith only [h16984, h18649, hlam]
                                  · linarith only [h18649, h7, hlam]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            rcases p18622_3 (m.d 0 4) (by simp) with h18652 | h18652
                            · linarith only [h14159, h18652, hlam]
                            · linarith only [h18652, h2, hlam]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            rcases p18622_3 (m.d 0 4) (by simp) with h18655 | h18655
                            · linarith only [h14159, h18655, hlam]
                            · linarith only [h18655, h5, hlam]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [h1, h16969, h7, hc23, hc45, hlam, hphi, ht34, p18622_1]
                          · have p18622_0 := h18622c.1
                            have p18622_1 := h18622c.2.1
                            have p18622_2 := h18622c.2.2.1
                            have p18622_3 := h18622c.2.2.2
                            linarith only [hlam, p18622_0]
                  · linarith only [h18615, hlam, p18574_0]
                · linarith only [h18614, h6, hlam]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h4, hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h16969, hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h16978, hlam, p18574_1]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h16980, hlam, p18574_1]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h5, hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h16970, hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h14159, h16970, h2, hc23, hc45, hlam, hphi, ht34, p18574_1]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h16982, hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h6, hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h16971, hlam, p18574_0]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h0, h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18574_1]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [h0, h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p18574_1]
              · have p18574_0 := h18574c.1
                have p18574_1 := h18574c.2.1
                have p18574_2 := h18574c.2.2.1
                have p18574_3 := h18574c.2.2.2
                linarith only [hlam, p18574_0]
            · linarith only [h18468, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p17727_1]
          · linarith only [h16976, h18467, hlam]
    · linarith only [h16970, h18462, hlam]
  · linarith only [h18461, h2, hlam]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x24 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 5) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 5) ∧ (m.d 1 5) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 5) ≤ z)))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases h1bigk with h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c | h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x2 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x3 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x4 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x5 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x6 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x7 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x8 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x9 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x10 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x11 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x12 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x13 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x14 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x15 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x16 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x17 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x18 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x19 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x20 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x21 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x22 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x23 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x24 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984 h17727c

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 3 4 5 (by decide) (by decide) with h16984 | h16984
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982 h16984

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 2 4 5 (by decide) (by decide) with h16982 | h16982
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980 h16982

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 2 3 5 (by decide) (by decide) with h16980 | h16980
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978 h16980

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 2 3 4 (by decide) (by decide) with h16978 | h16978
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976 h16978

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 1 4 5 (by decide) (by decide) with h16976 | h16976
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974 h16976

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 1 3 5 (by decide) (by decide) with h16974 | h16974
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972 h16974

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 1 3 4 (by decide) (by decide) with h16972 | h16972
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971 h16972

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 1 3 4 (by decide) (by decide) with h18682 | h18682
  · linarith only [h1, h18682, h7, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h18684 | h18684
    · linarith only [h1, h13284, h18684, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h18686 | h18686
      · linarith only [h14159, h18686, h2, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h18688 | h18688
        · linarith only [h1, h16969, h18688, h7, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h18690 | h18690
          · linarith only [h1, h13284, h16969, h16971, h18690, h6, h7, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h18692 | h18692
            · linarith only [h14159, h16970, h16971, h18692, h6, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h18694 | h18694
              · linarith only [h14159, h16970, h16971, h18688, h18694, h6, hc23, hc34, hlam, hphi]
              · rcases h1bigk with h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c | h18696c
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  rcases p18696_3 (m.d 0 1) (by simp) with h18698 | h18698
                  · rcases p18696_3 (m.d 1 2) (by simp) with h18699 | h18699
                    · linarith only [h18699, hlam, p18696_0]
                    · rcases p18696_3 (m.d 1 3) (by simp) with h18701 | h18701
                      · linarith only [h1, h18701, hlam]
                      · rcases p18696_3 (m.d 1 4) (by simp) with h18703 | h18703
                        · linarith only [h18703, h2, hlam]
                        · rcases p18696_3 (m.d 1 5) (by simp) with h18705 | h18705
                          · linarith only [h18705, h3, hlam]
                          · linarith only [h16971, h18705, hlam]
                  · linarith only [h18698, hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  rcases p18696_3 (m.d 0 1) (by simp) with h18709 | h18709
                  · rcases p18696_3 (m.d 1 2) (by simp) with h18710 | h18710
                    · linarith only [h0, h18710, hlam]
                    · linarith only [h16969, h18710, hlam]
                  · linarith only [h18709, hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  rcases p18696_3 (m.d 0 1) (by simp) with h18714 | h18714
                  · rcases p18696_3 (m.d 1 2) (by simp) with h18715 | h18715
                    · linarith only [h0, h18715, hlam]
                    · linarith only [h16970, h18715, hlam]
                  · linarith only [h18714, hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  rcases p18696_3 (m.d 0 1) (by simp) with h18719 | h18719
                  · rcases p18696_3 (m.d 1 2) (by simp) with h18720 | h18720
                    · linarith only [h0, h18720, hlam]
                    · rcases p18696_3 (m.d 1 3) (by simp) with h18722 | h18722
                      · linarith only [h1, h18722, hlam]
                      · rcases p18696_3 (m.d 1 4) (by simp) with h18724 | h18724
                        · linarith only [h18724, h2, hlam]
                        · rcases p18696_3 (m.d 1 5) (by simp) with h18726 | h18726
                          · linarith only [h18726, hlam, p18696_0]
                          · rcases h1emax with h18728 | h18728 | h18728 | h18728 | h18728
                            · linarith only [h0, h16970, h16971, h18688, h18728, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases h2bigk with h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c | h18730c
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [hlam, p18730_0]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                rcases p18730_3 (m.d 0 2) (by simp) with h18732 | h18732
                                · rcases p18730_3 (m.d 1 2) (by simp) with h18733 | h18733
                                  · linarith only [h0, h18733, hlam]
                                  · rcases p18730_3 (m.d 2 3) (by simp) with h18735 | h18735
                                    · linarith only [h18735, h4, hlam]
                                    · rcases p18730_3 (m.d 2 4) (by simp) with h18737 | h18737
                                      · linarith only [h18737, h5, hlam]
                                      · rcases p18730_3 (m.d 2 5) (by simp) with h18739 | h18739
                                        · linarith only [h18739, h6, hlam]
                                        · linarith only [h16971, h18739, hlam]
                                · linarith only [h0, h18732, hlam]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h16970, h16971, h18688, h6, hlam, p18730_2]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h16970, h16971, h6, hlam, p18730_2]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h0, h16970, h16971, h18688, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18730_1]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h0, hlam, p18730_1]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [hlam, p18730_0]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h13284, h16971, h6, hc23, hc35, hlam, hphi, p18730_1]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h13284, h16971, h18694, h6, hc24, hc45, hlam, hphi, p18730_1]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h16971, hlam, p18730_0]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h4, hlam, p18730_0]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h16969, hlam, p18730_0]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [hlam, p18730_0]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h18688, hlam, p18730_1]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h18690, hlam, p18730_1]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h5, hlam, p18730_0]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h16970, hlam, p18730_0]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h18694, h5, h7, hc23, hc45, hlam, hphi, ht34, p18730_1]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [hlam, p18730_0]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h18692, hlam, p18730_0]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h6, hlam, p18730_0]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [h13284, h16969, h18694, h6, hc23, hc45, hlam, hphi, ht34, p18730_1]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                rcases p18730_3 (m.d 0 2) (by simp) with h18763 | h18763
                                · rcases p18730_3 (m.d 1 2) (by simp) with h18764 | h18764
                                  · linarith only [h16971, h18764, hlam]
                                  · linarith only [h16969, h18764, hlam]
                                · linarith only [h18763, h4, hlam]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                rcases p18730_3 (m.d 0 2) (by simp) with h18768 | h18768
                                · rcases p18730_3 (m.d 1 2) (by simp) with h18769 | h18769
                                  · linarith only [h16971, h18769, hlam]
                                  · linarith only [h16970, h18769, hlam]
                                · linarith only [h18768, h5, hlam]
                              · have p18730_0 := h18730c.1
                                have p18730_1 := h18730c.2.1
                                have p18730_2 := h18730c.2.2.1
                                have p18730_3 := h18730c.2.2.2
                                linarith only [hlam, p18730_0]
                            · rcases h2bigk with h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c | h18774c
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [hlam, p18774_0]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                rcases p18774_3 (m.d 0 2) (by simp) with h18776 | h18776
                                · rcases p18774_3 (m.d 1 2) (by simp) with h18777 | h18777
                                  · linarith only [h0, h18777, hlam]
                                  · rcases p18774_3 (m.d 2 3) (by simp) with h18779 | h18779
                                    · linarith only [h18779, h4, hlam]
                                    · rcases p18774_3 (m.d 2 4) (by simp) with h18781 | h18781
                                      · linarith only [h18781, h5, hlam]
                                      · rcases p18774_3 (m.d 2 5) (by simp) with h18783 | h18783
                                        · linarith only [h18783, h6, hlam]
                                        · linarith only [h16971, h18783, hlam]
                                · linarith only [h0, h18776, hlam]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h16970, h16971, h18688, h6, hlam, p18774_2]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h16970, h16971, h6, hlam, p18774_2]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h16970, h16971, h18688, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18774_1]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h0, hlam, p18774_1]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [hlam, p18774_0]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18696_1, p18774_1]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h16971, h18688, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18696_1, p18774_1]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h16971, hlam, p18774_0]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h4, hlam, p18774_0]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h16969, hlam, p18774_0]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [hlam, p18774_0]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h18688, hlam, p18774_1]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h18690, hlam, p18774_1]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h5, hlam, p18774_0]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h16970, hlam, p18774_0]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h18694, h5, h7, hc23, hc45, hlam, hphi, ht34, p18774_1]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [hlam, p18774_0]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h18692, hlam, p18774_0]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h6, hlam, p18774_0]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [h0, h16969, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18774_1]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                rcases p18774_3 (m.d 0 2) (by simp) with h18807 | h18807
                                · rcases p18774_3 (m.d 1 2) (by simp) with h18808 | h18808
                                  · linarith only [h16971, h18808, hlam]
                                  · linarith only [h16969, h18808, hlam]
                                · linarith only [h18807, h4, hlam]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                rcases p18774_3 (m.d 0 2) (by simp) with h18812 | h18812
                                · rcases p18774_3 (m.d 1 2) (by simp) with h18813 | h18813
                                  · linarith only [h16971, h18813, hlam]
                                  · linarith only [h16970, h18813, hlam]
                                · linarith only [h18812, h5, hlam]
                              · have p18774_0 := h18774c.1
                                have p18774_1 := h18774c.2.1
                                have p18774_2 := h18774c.2.2.1
                                have p18774_3 := h18774c.2.2.2
                                linarith only [hlam, p18774_0]
                            · rcases h2bigk with h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c | h18818c
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [hlam, p18818_0]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                rcases p18818_3 (m.d 0 2) (by simp) with h18820 | h18820
                                · rcases p18818_3 (m.d 1 2) (by simp) with h18821 | h18821
                                  · linarith only [h0, h18821, hlam]
                                  · rcases p18818_3 (m.d 2 3) (by simp) with h18823 | h18823
                                    · linarith only [h18823, h4, hlam]
                                    · rcases p18818_3 (m.d 2 4) (by simp) with h18825 | h18825
                                      · linarith only [h18825, h5, hlam]
                                      · rcases p18818_3 (m.d 2 5) (by simp) with h18827 | h18827
                                        · linarith only [h18827, h6, hlam]
                                        · linarith only [h16971, h18827, hlam]
                                · linarith only [h0, h18820, hlam]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h16969, h16971, h6, hlam, p18818_2]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h16970, h16971, h6, hlam, p18818_2]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h0, h16970, h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p18818_1]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h0, hlam, p18818_1]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [hlam, p18818_0]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h0, h16971, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18818_1]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h0, h16971, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p18818_1]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h16971, hlam, p18818_0]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h4, hlam, p18818_0]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h16969, hlam, p18818_0]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [hlam, p18818_0]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h18688, hlam, p18818_1]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h18690, hlam, p18818_1]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h5, hlam, p18818_0]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h16970, hlam, p18818_0]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h18694, h5, h7, hc23, hc45, hlam, hphi, ht34, p18818_1]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [hlam, p18818_0]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h18692, hlam, p18818_0]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h6, hlam, p18818_0]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [h0, h16969, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18818_1]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                rcases p18818_3 (m.d 0 2) (by simp) with h18851 | h18851
                                · rcases p18818_3 (m.d 1 2) (by simp) with h18852 | h18852
                                  · linarith only [h16971, h18852, hlam]
                                  · linarith only [h16969, h18852, hlam]
                                · linarith only [h18851, h4, hlam]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                rcases p18818_3 (m.d 0 2) (by simp) with h18856 | h18856
                                · rcases p18818_3 (m.d 1 2) (by simp) with h18857 | h18857
                                  · linarith only [h16971, h18857, hlam]
                                  · linarith only [h16970, h18857, hlam]
                                · linarith only [h18856, h5, hlam]
                              · have p18818_0 := h18818c.1
                                have p18818_1 := h18818c.2.1
                                have p18818_2 := h18818c.2.2.1
                                have p18818_3 := h18818c.2.2.2
                                linarith only [hlam, p18818_0]
                            · rcases h2bigk with h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c | h18862c
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [hlam, p18862_0]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                rcases p18862_3 (m.d 0 2) (by simp) with h18864 | h18864
                                · rcases p18862_3 (m.d 1 2) (by simp) with h18865 | h18865
                                  · linarith only [h0, h18865, hlam]
                                  · rcases p18862_3 (m.d 2 3) (by simp) with h18867 | h18867
                                    · linarith only [h18867, h4, hlam]
                                    · rcases p18862_3 (m.d 2 4) (by simp) with h18869 | h18869
                                      · linarith only [h18869, h5, hlam]
                                      · rcases p18862_3 (m.d 2 5) (by simp) with h18871 | h18871
                                        · linarith only [h18871, h6, hlam]
                                        · linarith only [h16971, h18871, hlam]
                                · linarith only [h0, h18864, hlam]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h16970, h16971, h18688, h6, hlam, p18862_2]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h16970, h16971, h6, hlam, p18862_2]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h16970, h16971, h18688, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18862_1]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h0, hlam, p18862_1]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [hlam, p18862_0]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h0, h16971, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18862_1]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h0, h16971, h18688, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18862_1]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h16971, hlam, p18862_0]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h4, hlam, p18862_0]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h16969, hlam, p18862_0]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [hlam, p18862_0]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h18688, hlam, p18862_1]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h18690, hlam, p18862_1]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h5, hlam, p18862_0]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h16970, hlam, p18862_0]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h18694, h5, h7, hc23, hc45, hlam, hphi, ht34, p18862_1]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [hlam, p18862_0]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h18692, hlam, p18862_0]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h6, hlam, p18862_0]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [h0, h16969, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18862_1]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                rcases p18862_3 (m.d 0 2) (by simp) with h18895 | h18895
                                · rcases p18862_3 (m.d 1 2) (by simp) with h18896 | h18896
                                  · linarith only [h16971, h18896, hlam]
                                  · linarith only [h16969, h18896, hlam]
                                · linarith only [h18895, h4, hlam]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                rcases p18862_3 (m.d 0 2) (by simp) with h18900 | h18900
                                · rcases p18862_3 (m.d 1 2) (by simp) with h18901 | h18901
                                  · linarith only [h16971, h18901, hlam]
                                  · linarith only [h16970, h18901, hlam]
                                · linarith only [h18900, h5, hlam]
                              · have p18862_0 := h18862c.1
                                have p18862_1 := h18862c.2.1
                                have p18862_2 := h18862c.2.2.1
                                have p18862_3 := h18862c.2.2.2
                                linarith only [hlam, p18862_0]
                  · linarith only [h18719, hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h0, hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h0, h16969, h16971, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18696_1]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h0, h16970, h16971, h18688, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18696_1]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h16971, hlam, p18696_1]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h1, hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h16969, hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h18682, hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h18684, hlam, p18696_1]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h2, hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h16970, hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h16969, h18694, h2, h7, hc23, hc45, hlam, hphi, ht34, p18696_1]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h18686, hlam, p18696_1]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h3, hlam, p18696_0]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [h16969, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18696_1]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  rcases p18696_3 (m.d 0 1) (by simp) with h18924 | h18924
                  · rcases p18696_3 (m.d 1 2) (by simp) with h18925 | h18925
                    · linarith only [h16971, h18925, hlam]
                    · linarith only [h16969, h18925, hlam]
                  · linarith only [h1, h18924, hlam]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  rcases p18696_3 (m.d 0 1) (by simp) with h18929 | h18929
                  · rcases p18696_3 (m.d 1 2) (by simp) with h18930 | h18930
                    · linarith only [h16971, h18930, hlam]
                    · linarith only [h16970, h18930, hlam]
                  · linarith only [h18929, h2, hlam]
                · have p18696_0 := h18696c.1
                  have p18696_1 := h18696c.2.1
                  have p18696_2 := h18696c.2.2.1
                  have p18696_3 := h18696c.2.2.2
                  linarith only [hlam, p18696_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 1 2 5 (by decide) (by decide) with h16971 | h16971
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970 h16971

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  linarith only [h14159, h16969, h16970, h5, hc23, hc45, hlam, hphi, ht34]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 1 2 4 (by decide) (by decide) with h16970 | h16970
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969 h16970

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 1 2 4 (by decide) (by decide) with h18936 | h18936
  · linarith only [h14159, h16969, h18936, h4, h7, hc24, hc45, hlam, hphi]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h18938 | h18938
    · rcases m.htr 1 3 4 (by decide) (by decide) with h18939 | h18939
      · linarith only [h16969, h18938, h18939, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h18941 | h18941
        · linarith only [h13284, h16969, h18938, h18941, h4, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · linarith only [h16969, h18938, h18941, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h18944 | h18944
      · linarith only [h1, h16969, h18944, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h18946 | h18946
        · linarith only [h13284, h16969, h18946, h4, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h18948 | h18948
          · linarith only [h14159, h18936, h18948, h5, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h18950 | h18950
            · linarith only [h18950, h4, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h18952 | h18952
              · linarith only [h13284, h18952, h4, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h18954 | h18954
                · linarith only [h14159, h18954, h5, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h18956 | h18956
                  · linarith only [h14159, h16969, h18956, h4, h7, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h16969, h18956, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
