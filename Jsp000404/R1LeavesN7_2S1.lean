import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 5 (by decide) (by decide) with h478 | h478
  · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
    · rcases m.htr 2 3 4 (by decide) (by decide) with h480 | h480
      · linarith only [h0, h13, h4, h478, h480, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h482 | h482
        · rcases m.htr 2 4 5 (by decide) (by decide) with h483 | h483
          · rcases m.htr 3 4 5 (by decide) (by decide) with h484 | h484
            · rcases h0bigk with h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [hlam, p485_0]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h4, h482, h484, hc01, hc45, hlam, hphi, ht0b, ht5b, p485_1]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h10, h13, h482, h484, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p485_1]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h10, h13, h482, h484, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p485_1]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                rcases p485_3 (m.d 0 1) (by simp) with h490 | h490
                · rcases p485_3 (m.d 0 2) (by simp) with h491 | h491
                  · linarith only [h0, h491, hlam]
                  · linarith only [h491, h6, hlam]
                · linarith only [h3, h490, hlam]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h0, hlam, p485_0]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [hlam, p485_0]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h10, h13, h482, h484, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p485_1]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h0, h10, h13, h482, h484, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p485_1]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                rcases p485_3 (m.d 0 1) (by simp) with h499 | h499
                · rcases p485_3 (m.d 0 2) (by simp) with h500 | h500
                  · rcases p485_3 (m.d 0 3) (by simp) with h501 | h501
                    · linarith only [h4, h501, hlam]
                    · linarith only [h501, h8, hlam]
                  · linarith only [h500, h6, hlam]
                · linarith only [h3, h499, hlam]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h1, hlam, p485_1]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h4, hlam, p485_1]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [hlam, p485_0]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h10, h13, h482, h484, h7, hc03, hc45, hlam, hphi, ht0b, ht5b, p485_1]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                rcases p485_3 (m.d 0 1) (by simp) with h510 | h510
                · rcases p485_3 (m.d 0 2) (by simp) with h511 | h511
                  · rcases p485_3 (m.d 0 3) (by simp) with h512 | h512
                    · rcases p485_3 (m.d 0 4) (by simp) with h513 | h513
                      · linarith only [h513, h7, hlam]
                      · linarith only [h513, h9, hlam]
                    · linarith only [h512, h8, hlam]
                  · linarith only [h511, h6, hlam]
                · linarith only [h3, h510, hlam]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h2, hlam, p485_0]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h5, hlam, p485_0]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h7, hlam, p485_0]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [hlam, p485_0]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                rcases p485_3 (m.d 0 1) (by simp) with h523 | h523
                · rcases p485_3 (m.d 0 2) (by simp) with h524 | h524
                  · rcases p485_3 (m.d 0 3) (by simp) with h525 | h525
                    · rcases p485_3 (m.d 0 4) (by simp) with h526 | h526
                      · rcases p485_3 (m.d 0 5) (by simp) with h527 | h527
                        · linarith only [h527, h9, hlam]
                        · rcases h2bigk with h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h0, h10, h482, h484, hc01, hc45, hlam, hphi, ht0b, ht5b, p529_1]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            rcases p529_3 (m.d 0 2) (by simp) with h532 | h532
                            · rcases p529_3 (m.d 1 2) (by simp) with h533 | h533
                              · linarith only [h0, h533, hlam]
                              · linarith only [h10, h533, hlam]
                            · linarith only [h532, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            rcases p529_3 (m.d 0 2) (by simp) with h537 | h537
                            · rcases p529_3 (m.d 1 2) (by simp) with h538 | h538
                              · linarith only [h0, h538, hlam]
                              · linarith only [h11, h538, hlam]
                            · linarith only [h537, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            rcases p529_3 (m.d 0 2) (by simp) with h542 | h542
                            · rcases p529_3 (m.d 1 2) (by simp) with h543 | h543
                              · linarith only [h0, h543, hlam]
                              · linarith only [h12, h543, hlam]
                            · linarith only [h542, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h0, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h0, h482, h484, hc01, hc45, hlam, hphi, ht0b, ht5b, p529_1]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h0, h480, h482, h484, hc01, hc45, hlam, hphi, ht0b, ht5b, p529_1]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            rcases p529_3 (m.d 0 2) (by simp) with h551 | h551
                            · rcases p529_3 (m.d 1 2) (by simp) with h552 | h552
                              · rcases p529_3 (m.d 2 3) (by simp) with h553 | h553
                                · linarith only [h10, h553, hlam]
                                · linarith only [h482, h553, hlam]
                              · linarith only [h552, hlam, p529_0]
                            · linarith only [h551, h6, hlam]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h4, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h10, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h480, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p529_1]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h5, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h11, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h0, h482, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p529_1]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h0, h11, h482, h484, hc01, hc45, hlam, hphi, ht0b, ht5b, p529_1]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h6, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h12, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h482, hlam, p529_1]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [h483, hlam, p529_0]
                          · have p529_0 := h529c.1
                            have p529_1 := h529c.2.1
                            have p529_2 := h529c.2.2.1
                            have p529_3 := h529c.2.2.2
                            linarith only [hlam, p529_0]
                      · linarith only [h526, h9, hlam]
                    · linarith only [h525, h8, hlam]
                  · linarith only [h524, h6, hlam]
                · linarith only [h3, h523, hlam]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h3, hlam, p485_0]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h6, hlam, p485_1]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h8, hlam, p485_0]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [h9, hlam, p485_1]
              · have p485_0 := h485c.1
                have p485_1 := h485c.2.1
                have p485_2 := h485c.2.2.1
                have p485_3 := h485c.2.2.2
                linarith only [hlam, p485_0]
            · linarith only [h0, h10, h13, h4, h482, h484, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h13, h4, h478, h479, h480, h482, h483, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h13, h4, h478, h482, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h13, h478, h479, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h586 | h586
    · rcases m.htr 2 3 4 (by decide) (by decide) with h587 | h587
      · linarith only [h10, h13, h587, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h589 | h589
        · linarith only [h10, h478, h589, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h591 | h591
          · rcases m.htr 3 4 5 (by decide) (by decide) with h592 | h592
            · rcases h0bigk with h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [hlam, p593_0]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h5, h591, hc01, hc45, hlam, hphi, ht0b, ht5b, p593_1]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h478, h592, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p593_1]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                rcases p593_3 (m.d 0 1) (by simp) with h597 | h597
                · rcases p593_3 (m.d 0 2) (by simp) with h598 | h598
                  · linarith only [h0, h598, hlam]
                  · linarith only [h5, h598, hlam]
                · linarith only [h2, h597, hlam]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                rcases p593_3 (m.d 0 1) (by simp) with h602 | h602
                · rcases p593_3 (m.d 0 2) (by simp) with h603 | h603
                  · linarith only [h0, h603, hlam]
                  · linarith only [h6, h603, hlam]
                · linarith only [h3, h602, hlam]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h0, hlam, p593_0]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [hlam, p593_0]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h10, h478, h592, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p593_1]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                rcases p593_3 (m.d 0 1) (by simp) with h610 | h610
                · rcases p593_3 (m.d 0 2) (by simp) with h611 | h611
                  · rcases p593_3 (m.d 0 3) (by simp) with h612 | h612
                    · linarith only [h4, h612, hlam]
                    · linarith only [h612, h7, hlam]
                  · linarith only [h5, h611, hlam]
                · linarith only [h2, h610, hlam]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                rcases p593_3 (m.d 0 1) (by simp) with h617 | h617
                · rcases p593_3 (m.d 0 2) (by simp) with h618 | h618
                  · rcases p593_3 (m.d 0 3) (by simp) with h619 | h619
                    · linarith only [h4, h619, hlam]
                    · linarith only [h619, h8, hlam]
                  · linarith only [h6, h618, hlam]
                · linarith only [h3, h617, hlam]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h1, hlam, p593_1]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h4, hlam, p593_1]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [hlam, p593_0]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                rcases p593_3 (m.d 0 1) (by simp) with h627 | h627
                · rcases p593_3 (m.d 0 2) (by simp) with h628 | h628
                  · rcases p593_3 (m.d 0 3) (by simp) with h629 | h629
                    · rcases p593_3 (m.d 0 4) (by simp) with h630 | h630
                      · linarith only [h630, h7, hlam]
                      · rcases p593_3 (m.d 0 5) (by simp) with h632 | h632
                        · linarith only [h632, h8, hlam]
                        · rcases h2bigk with h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h0, h11, h591, hc01, hc45, hlam, hphi, ht0b, ht5b, p634_1]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h10, h4, h478, h592, h7, hlam, p593_1, p634_2]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            rcases p634_3 (m.d 0 2) (by simp) with h638 | h638
                            · rcases p634_3 (m.d 1 2) (by simp) with h639 | h639
                              · linarith only [h0, h639, hlam]
                              · linarith only [h11, h639, hlam]
                            · linarith only [h638, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            rcases p634_3 (m.d 0 2) (by simp) with h643 | h643
                            · rcases p634_3 (m.d 1 2) (by simp) with h644 | h644
                              · linarith only [h0, h644, hlam]
                              · linarith only [h12, h644, hlam]
                            · linarith only [h643, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h0, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            rcases p634_3 (m.d 0 2) (by simp) with h650 | h650
                            · rcases p634_3 (m.d 1 2) (by simp) with h651 | h651
                              · rcases p634_3 (m.d 2 3) (by simp) with h652 | h652
                                · linarith only [h652, hlam, p634_0]
                                · rcases p634_3 (m.d 2 4) (by simp) with h654 | h654
                                  · linarith only [h11, h654, hlam]
                                  · linarith only [h587, h654, hlam]
                              · linarith only [h651, hlam, p634_0]
                            · linarith only [h4, h650, hlam]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h0, h591, hc01, hc45, hlam, hphi, ht0b, ht5b, p634_1]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            rcases p634_3 (m.d 0 2) (by simp) with h660 | h660
                            · rcases p634_3 (m.d 1 2) (by simp) with h661 | h661
                              · rcases p634_3 (m.d 2 3) (by simp) with h662 | h662
                                · linarith only [h10, h662, hlam]
                                · rcases p634_3 (m.d 2 4) (by simp) with h664 | h664
                                  · linarith only [h11, h664, hlam]
                                  · linarith only [h591, h664, hlam]
                              · linarith only [h661, hlam, p634_0]
                            · linarith only [h6, h660, hlam]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h4, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h10, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h587, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h589, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h5, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h11, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h4, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p593_1, p634_1]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h0, h11, h2, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p593_1, p634_1]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h6, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h12, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p593_1, p634_1]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [h591, hlam, p634_0]
                          · have p634_0 := h634c.1
                            have p634_1 := h634c.2.1
                            have p634_2 := h634c.2.2.1
                            have p634_3 := h634c.2.2.2
                            linarith only [hlam, p634_0]
                    · linarith only [h629, h7, hlam]
                  · linarith only [h5, h628, hlam]
                · linarith only [h2, h627, hlam]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                rcases p593_3 (m.d 0 1) (by simp) with h687 | h687
                · rcases p593_3 (m.d 0 2) (by simp) with h688 | h688
                  · rcases p593_3 (m.d 0 3) (by simp) with h689 | h689
                    · rcases p593_3 (m.d 0 4) (by simp) with h690 | h690
                      · linarith only [h690, h7, hlam]
                      · linarith only [h690, h9, hlam]
                    · linarith only [h689, h8, hlam]
                  · linarith only [h6, h688, hlam]
                · linarith only [h3, h687, hlam]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h2, hlam, p593_0]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h5, hlam, p593_0]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h7, hlam, p593_0]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [hlam, p593_0]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                rcases p593_3 (m.d 0 1) (by simp) with h700 | h700
                · rcases p593_3 (m.d 0 2) (by simp) with h701 | h701
                  · rcases p593_3 (m.d 0 3) (by simp) with h702 | h702
                    · rcases p593_3 (m.d 0 4) (by simp) with h703 | h703
                      · rcases p593_3 (m.d 0 5) (by simp) with h704 | h704
                        · linarith only [h704, h9, hlam]
                        · rcases h2bigk with h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h0, h11, h591, hc01, hc45, hlam, hphi, ht0b, ht5b, p706_1]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h10, h478, h5, h8, hlam, p593_1, p706_2]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            rcases p706_3 (m.d 0 2) (by simp) with h710 | h710
                            · rcases p706_3 (m.d 1 2) (by simp) with h711 | h711
                              · linarith only [h0, h711, hlam]
                              · linarith only [h11, h711, hlam]
                            · linarith only [h710, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            rcases p706_3 (m.d 0 2) (by simp) with h715 | h715
                            · rcases p706_3 (m.d 1 2) (by simp) with h716 | h716
                              · linarith only [h0, h716, hlam]
                              · linarith only [h12, h716, hlam]
                            · linarith only [h715, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h0, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            rcases p706_3 (m.d 0 2) (by simp) with h722 | h722
                            · rcases p706_3 (m.d 1 2) (by simp) with h723 | h723
                              · rcases p706_3 (m.d 2 3) (by simp) with h724 | h724
                                · linarith only [h724, hlam, p706_0]
                                · rcases p706_3 (m.d 2 4) (by simp) with h726 | h726
                                  · linarith only [h11, h726, hlam]
                                  · linarith only [h587, h726, hlam]
                              · linarith only [h723, hlam, p706_0]
                            · linarith only [h4, h722, hlam]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h0, h591, hc01, hc45, hlam, hphi, ht0b, ht5b, p706_1]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            rcases p706_3 (m.d 0 2) (by simp) with h732 | h732
                            · rcases p706_3 (m.d 1 2) (by simp) with h733 | h733
                              · rcases p706_3 (m.d 2 3) (by simp) with h734 | h734
                                · linarith only [h10, h734, hlam]
                                · rcases p706_3 (m.d 2 4) (by simp) with h736 | h736
                                  · linarith only [h11, h736, hlam]
                                  · linarith only [h591, h736, hlam]
                              · linarith only [h733, hlam, p706_0]
                            · linarith only [h6, h732, hlam]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h4, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h10, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h587, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h589, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h5, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h11, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p706_1]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h0, h11, hc01, hc25, hlam, hphi, ht0b, ht5b, p706_1]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h6, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h12, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h4, h6, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p593_1, p706_1]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [h591, hlam, p706_0]
                          · have p706_0 := h706c.1
                            have p706_1 := h706c.2.1
                            have p706_2 := h706c.2.2.1
                            have p706_3 := h706c.2.2.2
                            linarith only [hlam, p706_0]
                      · linarith only [h703, h9, hlam]
                    · linarith only [h702, h8, hlam]
                  · linarith only [h6, h701, hlam]
                · linarith only [h3, h700, hlam]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h3, hlam, p593_0]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h6, hlam, p593_1]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h8, hlam, p593_0]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [h9, hlam, p593_1]
              · have p593_0 := h593c.1
                have p593_1 := h593c.2.1
                have p593_2 := h593c.2.2.1
                have p593_3 := h593c.2.2.2
                linarith only [hlam, p593_0]
            · linarith only [h13, h586, h592, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h766 | h766
            · rcases h0bigk with h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [hlam, p767_0]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h4, h478, h586, h591, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p767_1]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h478, h586, h591, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p767_1]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h591, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p767_1]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                rcases p767_3 (m.d 0 1) (by simp) with h772 | h772
                · rcases p767_3 (m.d 0 2) (by simp) with h773 | h773
                  · linarith only [h0, h773, hlam]
                  · linarith only [h6, h773, hlam]
                · linarith only [h3, h772, hlam]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h0, hlam, p767_0]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [hlam, p767_0]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h13, h586, h587, h591, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p767_1]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h0, h13, h586, h587, h591, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p767_1]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                rcases p767_3 (m.d 0 1) (by simp) with h781 | h781
                · rcases p767_3 (m.d 0 2) (by simp) with h782 | h782
                  · rcases p767_3 (m.d 0 3) (by simp) with h783 | h783
                    · linarith only [h4, h783, hlam]
                    · linarith only [h783, h8, hlam]
                  · linarith only [h6, h782, hlam]
                · linarith only [h3, h781, hlam]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h1, hlam, p767_1]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h4, hlam, p767_1]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [hlam, p767_0]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h13, h586, h587, h591, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p767_1]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                rcases p767_3 (m.d 0 1) (by simp) with h792 | h792
                · rcases p767_3 (m.d 0 2) (by simp) with h793 | h793
                  · rcases p767_3 (m.d 0 3) (by simp) with h794 | h794
                    · rcases p767_3 (m.d 0 4) (by simp) with h795 | h795
                      · linarith only [h7, h795, hlam]
                      · linarith only [h795, h9, hlam]
                    · linarith only [h794, h8, hlam]
                  · linarith only [h6, h793, hlam]
                · linarith only [h3, h792, hlam]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h2, hlam, p767_0]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h5, hlam, p767_0]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h7, hlam, p767_0]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [hlam, p767_0]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                rcases p767_3 (m.d 0 1) (by simp) with h805 | h805
                · rcases p767_3 (m.d 0 2) (by simp) with h806 | h806
                  · rcases p767_3 (m.d 0 3) (by simp) with h807 | h807
                    · rcases p767_3 (m.d 0 4) (by simp) with h808 | h808
                      · rcases p767_3 (m.d 0 5) (by simp) with h809 | h809
                        · linarith only [h809, h9, hlam]
                        · rcases h2bigk with h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h0, h11, h586, h587, h591, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p811_1]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h478, h5, h586, h587, h591, h8, hlam, p767_1, p811_2]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h478, h5, h586, h591, h8, hlam, p767_1, p811_2]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            rcases p811_3 (m.d 0 2) (by simp) with h816 | h816
                            · rcases p811_3 (m.d 1 2) (by simp) with h817 | h817
                              · linarith only [h0, h817, hlam]
                              · linarith only [h12, h817, hlam]
                            · linarith only [h816, hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h0, hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            rcases p811_3 (m.d 0 2) (by simp) with h823 | h823
                            · rcases p811_3 (m.d 1 2) (by simp) with h824 | h824
                              · rcases p811_3 (m.d 2 3) (by simp) with h825 | h825
                                · linarith only [h825, hlam, p811_0]
                                · rcases p811_3 (m.d 2 4) (by simp) with h827 | h827
                                  · linarith only [h11, h827, hlam]
                                  · linarith only [h587, h827, hlam]
                              · linarith only [h824, hlam, p811_0]
                            · linarith only [h4, h823, hlam]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            rcases p811_3 (m.d 0 2) (by simp) with h832 | h832
                            · rcases p811_3 (m.d 1 2) (by simp) with h833 | h833
                              · rcases p811_3 (m.d 2 3) (by simp) with h834 | h834
                                · linarith only [h10, h834, hlam]
                                · rcases p811_3 (m.d 2 4) (by simp) with h836 | h836
                                  · linarith only [h836, hlam, p811_0]
                                  · rcases p811_3 (m.d 2 5) (by simp) with h838 | h838
                                    · linarith only [h12, h838, hlam]
                                    · linarith only [h591, h838, hlam]
                              · linarith only [h833, hlam, p811_0]
                            · linarith only [h5, h832, hlam]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            rcases p811_3 (m.d 0 2) (by simp) with h843 | h843
                            · rcases p811_3 (m.d 1 2) (by simp) with h844 | h844
                              · rcases p811_3 (m.d 2 3) (by simp) with h845 | h845
                                · linarith only [h10, h845, hlam]
                                · rcases p811_3 (m.d 2 4) (by simp) with h847 | h847
                                  · linarith only [h11, h847, hlam]
                                  · rcases p811_3 (m.d 2 5) (by simp) with h849 | h849
                                    · linarith only [h849, hlam, p811_0]
                                    · rcases h3bigk with h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        rcases p851_3 (m.d 0 3) (by simp) with h853 | h853
                                        · rcases p851_3 (m.d 1 3) (by simp) with h854 | h854
                                          · linarith only [h1, h854, hlam]
                                          · rcases p851_3 (m.d 2 3) (by simp) with h856 | h856
                                            · linarith only [h4, h856, hlam]
                                            · rcases p851_3 (m.d 3 4) (by simp) with h858 | h858
                                              · linarith only [h7, h858, hlam]
                                              · linarith only [h13, h858, hlam]
                                        · linarith only [h1, h853, hlam]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        rcases p851_3 (m.d 0 3) (by simp) with h862 | h862
                                        · rcases p851_3 (m.d 1 3) (by simp) with h863 | h863
                                          · linarith only [h1, h863, hlam]
                                          · linarith only [h10, h863, hlam]
                                        · linarith only [h4, h862, hlam]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h13, h4, h586, h587, h591, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p851_1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h0, h4, h478, h586, h587, h591, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p851_1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h1, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p851_1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h13, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h478, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h4, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h10, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h587, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h589, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h7, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p851_1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p851_1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h0, h4, h478, h586, h587, h591, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p851_1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h8, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h10, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p767_1, p851_1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h0, h4, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p767_1, p851_1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h766, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [hlam, p851_0]
                              · linarith only [h844, hlam, p811_0]
                            · linarith only [h6, h843, hlam]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h4, hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h10, hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h587, hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h589, hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h5, hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h11, hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h586, h591, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p811_1]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h591, hlam, p811_1]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h6, hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h12, hlam, p811_0]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h0, h4, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p767_1, p811_1]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [h0, h4, h478, h586, h591, h7, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p767_1, p811_1]
                          · have p811_0 := h811c.1
                            have p811_1 := h811c.2.1
                            have p811_2 := h811c.2.2.1
                            have p811_3 := h811c.2.2.2
                            linarith only [hlam, p811_0]
                      · linarith only [h808, h9, hlam]
                    · linarith only [h8, h807, hlam]
                  · linarith only [h6, h806, hlam]
                · linarith only [h3, h805, hlam]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h3, hlam, p767_0]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h6, hlam, p767_1]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h8, hlam, p767_0]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [h9, hlam, p767_1]
              · have p767_0 := h767c.1
                have p767_1 := h767c.2.1
                have p767_2 := h767c.2.2.1
                have p767_3 := h767c.2.2.2
                linarith only [hlam, p767_0]
            · linarith only [h13, h586, h766, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h916 | h916
      · linarith only [h10, h13, h916, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h918 | h918
        · linarith only [h10, h478, h918, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h920 | h920
          · linarith only [h0, h11, h586, h920, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h922 | h922
            · rcases h0bigk with h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [hlam, p923_0]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h13, h4, h586, h7, h922, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p923_1]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h10, h13, h586, h7, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p923_1]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h10, h13, h586, h7, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p923_1]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                rcases p923_3 (m.d 0 1) (by simp) with h928 | h928
                · rcases p923_3 (m.d 0 2) (by simp) with h929 | h929
                  · linarith only [h0, h929, hlam]
                  · linarith only [h6, h929, hlam]
                · linarith only [h3, h928, hlam]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h0, hlam, p923_0]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [hlam, p923_0]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h10, h13, h586, h7, h922, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p923_1]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h0, h10, h13, h586, h7, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p923_1]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                rcases p923_3 (m.d 0 1) (by simp) with h937 | h937
                · rcases p923_3 (m.d 0 2) (by simp) with h938 | h938
                  · rcases p923_3 (m.d 0 3) (by simp) with h939 | h939
                    · linarith only [h4, h939, hlam]
                    · linarith only [h8, h939, hlam]
                  · linarith only [h6, h938, hlam]
                · linarith only [h3, h937, hlam]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h1, hlam, p923_1]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h4, hlam, p923_1]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [hlam, p923_0]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h10, h13, h586, h7, h922, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p923_1]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                rcases p923_3 (m.d 0 1) (by simp) with h948 | h948
                · rcases p923_3 (m.d 0 2) (by simp) with h949 | h949
                  · rcases p923_3 (m.d 0 3) (by simp) with h950 | h950
                    · rcases p923_3 (m.d 0 4) (by simp) with h951 | h951
                      · linarith only [h7, h951, hlam]
                      · linarith only [h9, h951, hlam]
                    · linarith only [h8, h950, hlam]
                  · linarith only [h6, h949, hlam]
                · linarith only [h3, h948, hlam]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h2, hlam, p923_0]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h5, hlam, p923_0]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h7, hlam, p923_0]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [hlam, p923_0]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                rcases p923_3 (m.d 0 1) (by simp) with h961 | h961
                · rcases p923_3 (m.d 0 2) (by simp) with h962 | h962
                  · rcases p923_3 (m.d 0 3) (by simp) with h963 | h963
                    · rcases p923_3 (m.d 0 4) (by simp) with h964 | h964
                      · rcases p923_3 (m.d 0 5) (by simp) with h965 | h965
                        · linarith only [h9, h965, hlam]
                        · rcases h2bigk with h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            rcases p967_3 (m.d 0 2) (by simp) with h969 | h969
                            · rcases p967_3 (m.d 1 2) (by simp) with h970 | h970
                              · linarith only [h0, h970, hlam]
                              · rcases p967_3 (m.d 2 3) (by simp) with h972 | h972
                                · linarith only [h4, h972, hlam]
                                · rcases p967_3 (m.d 2 4) (by simp) with h974 | h974
                                  · linarith only [h5, h974, hlam]
                                  · rcases p967_3 (m.d 2 5) (by simp) with h976 | h976
                                    · linarith only [h6, h976, hlam]
                                    · rcases h3bigk with h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c | h978c
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        rcases p978_3 (m.d 0 3) (by simp) with h980 | h980
                                        · rcases p978_3 (m.d 1 3) (by simp) with h981 | h981
                                          · linarith only [h1, h981, hlam]
                                          · rcases p978_3 (m.d 2 3) (by simp) with h983 | h983
                                            · linarith only [h4, h983, hlam]
                                            · rcases p978_3 (m.d 3 4) (by simp) with h985 | h985
                                              · linarith only [h7, h985, hlam]
                                              · linarith only [h13, h985, hlam]
                                        · linarith only [h1, h980, hlam]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        rcases p978_3 (m.d 0 3) (by simp) with h989 | h989
                                        · rcases p978_3 (m.d 1 3) (by simp) with h990 | h990
                                          · linarith only [h1, h990, hlam]
                                          · linarith only [h10, h990, hlam]
                                        · linarith only [h4, h989, hlam]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h0, h10, h13, h4, h586, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p978_1]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h0, h10, h13, h4, h586, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p978_1]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h1, hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h13, h586, h8, h922, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p923_1, p978_1]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h13, hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h478, hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h4, hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h10, hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h916, hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h918, hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h7, hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p978_1]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p978_1]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h0, h4, h586, h7, h922, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p978_1]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h8, hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h10, hc23, hc35, hlam, hphi, p978_1]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h0, h4, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p923_1, p978_1]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [h922, hlam, p978_0]
                                      · have p978_0 := h978c.1
                                        have p978_1 := h978c.2.1
                                        have p978_2 := h978c.2.2.1
                                        have p978_3 := h978c.2.2.2
                                        linarith only [hlam, p978_0]
                            · linarith only [h0, h969, hlam]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h11, h4, h586, h7, h9, h916, hlam, p923_1, p967_2]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h11, h4, h586, h7, h9, hlam, p923_1, p967_2]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            rcases p967_3 (m.d 0 2) (by simp) with h1019 | h1019
                            · rcases p967_3 (m.d 1 2) (by simp) with h1020 | h1020
                              · linarith only [h0, h1020, hlam]
                              · linarith only [h1020, h12, hlam]
                            · linarith only [h1019, hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h0, hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            rcases p967_3 (m.d 0 2) (by simp) with h1026 | h1026
                            · rcases p967_3 (m.d 1 2) (by simp) with h1027 | h1027
                              · rcases p967_3 (m.d 2 3) (by simp) with h1028 | h1028
                                · linarith only [h1028, hlam, p967_0]
                                · rcases p967_3 (m.d 2 4) (by simp) with h1030 | h1030
                                  · linarith only [h1030, h11, hlam]
                                  · linarith only [h1030, h916, hlam]
                              · linarith only [h1027, hlam, p967_0]
                            · linarith only [h1026, h4, hlam]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            rcases p967_3 (m.d 0 2) (by simp) with h1035 | h1035
                            · rcases p967_3 (m.d 1 2) (by simp) with h1036 | h1036
                              · rcases p967_3 (m.d 2 3) (by simp) with h1037 | h1037
                                · linarith only [h10, h1037, hlam]
                                · rcases p967_3 (m.d 2 4) (by simp) with h1039 | h1039
                                  · linarith only [h1039, hlam, p967_0]
                                  · rcases p967_3 (m.d 2 5) (by simp) with h1041 | h1041
                                    · linarith only [h1041, h12, hlam]
                                    · linarith only [h1041, h920, hlam]
                              · linarith only [h1036, hlam, p967_0]
                            · linarith only [h1035, h5, hlam]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            rcases p967_3 (m.d 0 2) (by simp) with h1046 | h1046
                            · rcases p967_3 (m.d 1 2) (by simp) with h1047 | h1047
                              · rcases p967_3 (m.d 2 3) (by simp) with h1048 | h1048
                                · linarith only [h10, h1048, hlam]
                                · rcases p967_3 (m.d 2 4) (by simp) with h1050 | h1050
                                  · linarith only [h1050, h11, hlam]
                                  · rcases p967_3 (m.d 2 5) (by simp) with h1052 | h1052
                                    · linarith only [h1052, hlam, p967_0]
                                    · rcases h3bigk with h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        rcases p1054_3 (m.d 0 3) (by simp) with h1056 | h1056
                                        · rcases p1054_3 (m.d 1 3) (by simp) with h1057 | h1057
                                          · linarith only [h1, h1057, hlam]
                                          · rcases p1054_3 (m.d 2 3) (by simp) with h1059 | h1059
                                            · linarith only [h1059, h4, hlam]
                                            · rcases p1054_3 (m.d 3 4) (by simp) with h1061 | h1061
                                              · linarith only [h1061, h7, hlam]
                                              · linarith only [h1061, h13, hlam]
                                        · linarith only [h1, h1056, hlam]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        rcases p1054_3 (m.d 0 3) (by simp) with h1065 | h1065
                                        · rcases p1054_3 (m.d 1 3) (by simp) with h1066 | h1066
                                          · linarith only [h1, h1066, hlam]
                                          · linarith only [h10, h1066, hlam]
                                        · linarith only [h1065, h4, hlam]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h0, h13, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1054_1]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h0, h4, h586, h922, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1054_1]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h1, hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h13, hc23, hc34, hlam, hphi, p1054_1]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h13, hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h478, hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h4, hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h10, hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h916, hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h918, hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h7, hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p1054_1]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1054_1]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h0, h10, h13, h4, h586, h7, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1054_1]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h8, hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h10, hc23, hc35, hlam, hphi, p1054_1]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h0, h4, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1054_1, p923_1]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [h922, hlam, p1054_0]
                                      · have p1054_0 := h1054c.1
                                        have p1054_1 := h1054c.2.1
                                        have p1054_2 := h1054c.2.2.1
                                        have p1054_3 := h1054c.2.2.2
                                        linarith only [hlam, p1054_0]
                              · linarith only [h1047, hlam, p967_0]
                            · linarith only [h1046, h6, hlam]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h4, hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h10, hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h916, hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h918, hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h5, hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h11, hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p967_1]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h920, hlam, p967_1]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h6, hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h12, hlam, p967_0]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h0, h12, h3, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p923_1, p967_1]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [h0, h12, h4, h478, h7, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p923_1, p967_1]
                          · have p967_0 := h967c.1
                            have p967_1 := h967c.2.1
                            have p967_2 := h967c.2.2.1
                            have p967_3 := h967c.2.2.2
                            linarith only [hlam, p967_0]
                      · linarith only [h9, h964, hlam]
                    · linarith only [h8, h963, hlam]
                  · linarith only [h6, h962, hlam]
                · linarith only [h3, h961, hlam]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h3, hlam, p923_0]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h6, hlam, p923_1]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h8, hlam, p923_0]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [h9, hlam, p923_1]
              · have p923_0 := h923c.1
                have p923_1 := h923c.2.1
                have p923_2 := h923c.2.2.1
                have p923_3 := h923c.2.2.2
                linarith only [hlam, p923_0]
            · rcases h0bigk with h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [hlam, p1118_0]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h10, h13, h6, h9, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h10, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h10, h13, h9, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h10, h13, h9, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h0, hlam, p1118_0]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [hlam, p1118_0]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h0, h10, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h0, h10, h13, h9, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h0, h10, h13, h9, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h1, hlam, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h4, hlam, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [hlam, p1118_0]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h10, h13, h9, h922, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h0, h10, h13, h4, h9, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h2, hlam, p1118_0]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h5, hlam, p1118_0]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h7, hlam, p1118_0]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [hlam, p1118_0]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h0, h10, h13, h4, h7, h9, h922, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h3, hlam, p1118_0]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h6, hlam, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h8, hlam, p1118_0]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [h9, hlam, p1118_1]
              · have p1118_0 := h1118c.1
                have p1118_1 := h1118c.2.1
                have p1118_2 := h1118c.2.2.1
                have p1118_3 := h1118c.2.2.2
                linarith only [hlam, p1118_0]

set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12 h13
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12 h13

set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 4 (by decide) (by decide) with h1144 | h1144
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1145 | h1145
    · linarith only [h10, h1145, h12, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1147 | h1147
      · linarith only [h11, h1147, h12, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1149 | h1149
        · linarith only [h0, h10, h1149, h12, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h10, h1144, h1149, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1152 | h1152
    · linarith only [h11, h1144, h1152, h12, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1154 | h1154
      · linarith only [h11, h1154, h12, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1156 | h1156
        · linarith only [h0, h10, h1144, h1156, h12, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1158 | h1158
          · linarith only [h10, h1152, h1158, h12, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1160 | h1160
            · linarith only [h0, h11, h1158, h1160, h12, h4, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1162 | h1162
              · linarith only [h0, h11, h1156, h1160, h1162, h12, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases h0bigk with h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h11, h1156, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h1144, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h11, h1156, h1158, h1162, h12, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h11, h1156, h1158, h1162, h12, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h0, hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h11, h1156, h1158, h12, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h0, h11, h1156, h1158, h1162, h12, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h0, h11, h1156, h1158, h1162, h12, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h1, hlam, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h4, hlam, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h11, h1156, h1158, h1162, h12, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h0, h11, h1156, h1158, h1162, h12, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h2, hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h5, hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h7, hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h11, h1156, h1158, h1162, h12, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h3, hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h6, hlam, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h8, hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h9, hlam, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [hlam, p1164_0]

set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12

end R2N4
