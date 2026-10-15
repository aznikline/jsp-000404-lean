import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_29S1
import Jsp000404.R1LeavesN7_29S2
import Jsp000404.R1LeavesN7_29S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6334000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1951 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2940 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3280 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3841 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h4487 | h4487
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4488 | h4488
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4489 | h4489
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4490 | h4490
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4491 | h4491
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4492 | h4492
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4493 | h4493
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4494 | h4494
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4495 | h4495
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4496 | h4496
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4497 | h4497
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4498 | h4498
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4499 | h4499
                          · linarith only [h3841, h4487, h4492, h4499, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h3841, h4487, h4491, h4492, h4499, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h3841, h4498, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h3841, h4489, h4497, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1951, h4490, h4496, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                  · linarith only [h3841, h4487, h4489, h4492, h4495, hlam]
                · linarith only [h3841, h4488, h4492, h4494, hlam]
              · linarith only [h3841, h4492, h4493, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4508 | h4508
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4509 | h4509
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4510 | h4510
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4511 | h4511
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4512 | h4512
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4513 | h4513
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4514 | h4514
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4515 | h4515
                            · rcases h0bigk with h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [hlam, p4516_0]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h0, hlam, p4516_1]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h1951, hlam, p4516_0]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h2940, hlam, p4516_1]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h3280, hlam, p4516_1]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h0, h4492, hc01, hc23, hlam, hphi, ht12, p4516_1]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [hlam, p4516_0]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h3841, hlam, p4516_0]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h0, h4487, h4492, h4512, h4515, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4516_1]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h0, h3280, h4492, hc01, hc23, hlam, hphi, ht12, p4516_1]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                rcases p4516_3 (m.d 0 1) (by simp) with h4527 | h4527
                                · linarith only [h1951, h4527, hlam]
                                · rcases p4516_3 (m.d 0 2) (by simp) with h4529 | h4529
                                  · linarith only [h3841, h4529, hlam]
                                  · linarith only [h0, h4529, hlam]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h4487, h4512, h4515, hc45, hlam, hphi, ht0b, ht5b, p4516_1, u0elo2]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [hlam, p4516_0]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h4487, h4512, h4515, hc45, hlam, hphi, ht0b, ht5b, p4516_1, u0elo2]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                rcases p4516_3 (m.d 0 1) (by simp) with h4535 | h4535
                                · linarith only [h1951, h4535, hlam]
                                · rcases p4516_3 (m.d 0 2) (by simp) with h4537 | h4537
                                  · linarith only [h3841, h4537, hlam]
                                  · linarith only [h4488, h4537, hlam]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h0, h4487, h4492, hc01, hc23, hlam, hphi, ht12, p4516_1]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h4487, hlam, p4516_0]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h4489, hlam, p4516_0]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [hlam, p4516_0]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h0, h3280, h4487, h4492, hc01, hc23, hlam, hphi, ht12, p4516_1]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4516_1, u5elo0]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h4488, hlam, p4516_1]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h4490, hlam, p4516_0]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [h4491, hlam, p4516_1]
                              · have p4516_0 := h4516c.1
                                have p4516_1 := h4516c.2.1
                                have p4516_2 := h4516c.2.2.1
                                have p4516_3 := h4516c.2.2.2
                                linarith only [hlam, p4516_0]
                            · linarith only [h0, h4487, h4492, h4514, h4515, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4551 | h4551
                            · linarith only [h4512, h4514, h4551, hlam]
                            · rcases h0bigk with h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c | h4553c
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [hlam, p4553_0]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h0, hlam, p4553_1]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h1951, hlam, p4553_0]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h2940, hlam, p4553_1]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h3280, hlam, p4553_1]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h0, h4492, hc01, hc23, hlam, hphi, ht12, p4553_1]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [hlam, p4553_0]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h3841, hlam, p4553_0]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h0, h4491, h4492, h4512, h4514, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4553_1]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h0, h3280, h4492, hc01, hc23, hlam, hphi, ht12, p4553_1]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                rcases p4553_3 (m.d 0 1) (by simp) with h4564 | h4564
                                · linarith only [h1951, h4564, hlam]
                                · rcases p4553_3 (m.d 0 2) (by simp) with h4566 | h4566
                                  · linarith only [h3841, h4566, hlam]
                                  · linarith only [h0, h4566, hlam]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h4487, h4512, hc34, hlam, hphi, ht0b, ht45, ht5b, p4553_1, u0elo2]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [hlam, p4553_0]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h4491, h4512, h4514, hc34, hlam, hphi, ht0b, ht45, ht5b, p4553_1, u0elo2]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h4491, h4512, h4514, hc34, hlam, hphi, ht0b, ht45, ht5b, p4553_1, u0elo2]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h0, h4487, h4492, hc01, hc23, hlam, hphi, ht12, p4553_1]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h4487, hlam, p4553_0]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h4489, hlam, p4553_0]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [hlam, p4553_0]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h0, h4487, h4491, h4492, h4512, h4514, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4553_1]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4553_1, u5elo0]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h4488, hlam, p4553_1]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h4490, hlam, p4553_0]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [h4491, hlam, p4553_1]
                              · have p4553_0 := h4553c.1
                                have p4553_1 := h4553c.2.1
                                have p4553_2 := h4553c.2.2.1
                                have p4553_3 := h4553c.2.2.2
                                linarith only [hlam, p4553_0]
                        · linarith only [h0, h4487, h4491, h4492, h4513, hc45, hlam, hphi, u5elo3]
                      · linarith only [h2940, h4492, h4508, h4512, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h1951, h4487, h4490, h4491, h4492, h4511, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1951, h4489, h4510, hlam]
                · linarith only [h0, h4488, h4509, hlam]
              · linarith only [h0, h4487, h4508, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4589 | h4589
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4590 | h4590
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4591 | h4591
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4592 | h4592
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4593 | h4593
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4594 | h4594
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4595 | h4595
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4596 | h4596
                          · linarith only [h4487, h4491, h4596, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4598 | h4598
                            · linarith only [h2940, h3841, h4488, h4491, h4589, h4594, h4596, h4598, hc01, hc12, hlam, hphi]
                            · rcases h0bigk with h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [hlam, p4600_0]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h0, hlam, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h1951, hlam, p4600_0]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h2940, hlam, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h3280, hlam, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h3841, h4589, hc01, hc12, hlam, hphi, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [hlam, p4600_0]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h3841, hlam, p4600_0]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h2940, h3841, h4589, hc01, hc12, hlam, hphi, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h3841, h4589, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h3841, h4589, hc01, hc12, hlam, hphi, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h3841, h4488, h4589, h4596, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [hlam, p4600_0]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h2940, h3841, h4589, hc01, hc12, hlam, hphi, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h3280, h3841, h4589, hc01, hc12, hlam, hphi, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h4491, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h4487, hlam, p4600_0]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h4489, hlam, p4600_0]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [hlam, p4600_0]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h4491, hlam, p4600_0]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4600_1, u5elo0]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h4488, hlam, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h4490, hlam, p4600_0]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [h3841, h4488, h4589, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4600_1]
                              · have p4600_0 := h4600c.1
                                have p4600_1 := h4600c.2.1
                                have p4600_2 := h4600c.2.2.1
                                have p4600_3 := h4600c.2.2.2
                                linarith only [hlam, p4600_0]
                        · linarith only [h3841, h4595, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h3841, h4489, h4594, hlam]
                    · linarith only [h3841, h4488, h4490, h4589, h4593, hlam]
                  · linarith only [h3841, h4487, h4489, h4491, h4589, h4592, hc24, hlam, hphi, ht45, u5elo4]
                · linarith only [h3841, h4488, h4591, hc12, hc23, hlam, hphi]
              · linarith only [h3841, h4589, h4590, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4632 | h4632
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4633 | h4633
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4634 | h4634
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4635 | h4635
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4636 | h4636
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4637 | h4637
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4638 | h4638
                          · linarith only [h4487, h4491, h4638, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4640 | h4640
                            · linarith only [h2940, h4489, h4491, h4640, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [hlam, p4642_0]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h0, hlam, p4642_1]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h1951, hlam, p4642_0]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h2940, hlam, p4642_1]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h3280, hlam, p4642_1]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h3841, hc01, hc23, hlam, hphi, ht12, p4642_1]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [hlam, p4642_0]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h3841, hlam, p4642_0]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h2940, h3841, hc01, hc23, hlam, hphi, ht12, p4642_1]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h2940, h3841, h4491, hc01, hc23, hlam, hphi, ht12, p4642_1]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                rcases p4642_3 (m.d 0 1) (by simp) with h4653 | h4653
                                · linarith only [h1951, h4653, hlam]
                                · rcases p4642_3 (m.d 0 2) (by simp) with h4655 | h4655
                                  · linarith only [h3841, h4655, hlam]
                                  · linarith only [h0, h4655, hlam]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h4487, hc24, hlam, hphi, ht0b, ht45, ht5b, p4642_1, u0elo2]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [hlam, p4642_0]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                rcases p4642_3 (m.d 0 1) (by simp) with h4660 | h4660
                                · linarith only [h1951, h4660, hlam]
                                · rcases p4642_3 (m.d 0 2) (by simp) with h4662 | h4662
                                  · linarith only [h3841, h4662, hlam]
                                  · linarith only [h4487, h4662, hlam]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                rcases p4642_3 (m.d 0 1) (by simp) with h4665 | h4665
                                · linarith only [h1951, h4665, hlam]
                                · rcases p4642_3 (m.d 0 2) (by simp) with h4667 | h4667
                                  · linarith only [h3841, h4667, hlam]
                                  · linarith only [h4488, h4667, hlam]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h4491, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4642_1]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h4487, hlam, p4642_0]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h4489, hlam, p4642_0]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [hlam, p4642_0]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h4491, hlam, p4642_0]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h3280, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4642_1, u5elo1]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h4488, hlam, p4642_1]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h4490, hlam, p4642_0]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [h3280, hc04, hlam, hphi, ht45, p4642_1, u5elo1]
                              · have p4642_0 := h4642c.1
                                have p4642_1 := h4642c.2.1
                                have p4642_2 := h4642c.2.2.1
                                have p4642_3 := h4642c.2.2.2
                                linarith only [hlam, p4642_0]
                        · linarith only [h4589, h4637, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h4589, h4636, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1951, h4490, h4635, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                  · linarith only [h1951, h3841, h4487, h4489, h4634, hlam]
                · linarith only [h0, h4488, h4633, hlam]
              · linarith only [h0, h4487, h4632, hlam]
        · linarith only [h3841, h4487, h4490, hc24, hlam, hphi, ht45, u5elo3]
      · linarith only [h3841, h4487, h4489, hlam]
    · linarith only [h4487, h4488, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4689 | h4689
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4690 | h4690
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4691 | h4691
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4692 | h4692
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4693 | h4693
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4694 | h4694
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4695 | h4695
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4696 | h4696
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4697 | h4697
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4698 | h4698
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4699 | h4699
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4700 | h4700
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4701 | h4701
                            · rcases h0bigk with h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c | h4702c
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [hlam, p4702_0]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h0, hlam, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h1951, hlam, p4702_0]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h2940, hlam, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h3280, hlam, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h4487, h4693, h4698, hc01, hc12, hlam, hphi, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [hlam, p4702_0]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h3841, hlam, p4702_0]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h4487, hlam, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h4487, h4693, h4698, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h3841, h4693, hc01, hc12, hlam, hphi, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h3841, h4689, h4693, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [hlam, p4702_0]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h2940, h3841, h4693, hc01, hc12, hlam, hphi, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h3280, h3841, h4693, hc01, hc12, hlam, hphi, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h4487, h4693, h4698, hc01, hc12, hlam, hphi, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h4487, h4689, h4693, h4698, h4699, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h4690, hlam, p4702_0]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [hlam, p4702_0]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h3280, h4487, h4693, h4698, hc01, hc12, hlam, hphi, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4702_1, u5elo0]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h4689, hlam, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h4691, hlam, p4702_0]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [h4692, hlam, p4702_1]
                              · have p4702_0 := h4702c.1
                                have p4702_1 := h4702c.2.1
                                have p4702_2 := h4702c.2.2.1
                                have p4702_3 := h4702c.2.2.2
                                linarith only [hlam, p4702_0]
                            · linarith only [h4487, h4689, h4693, h4698, h4700, h4701, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h4487, h4689, h4692, h4700, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h4487, h4689, h4698, h4699, hc25, hlam, hphi, u5elo3]
                      · linarith only [h3841, h4690, h4698, hlam]
                    · linarith only [h3841, h4690, h4691, h4693, h4697, hc34, hlam, hphi, ht45, u5elo0]
                  · linarith only [h3841, h4689, h4690, h4693, h4696, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h3841, h4689, h4693, h4695, hlam]
              · linarith only [h3841, h4689, h4693, h4694, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4736 | h4736
              · linarith only [h4487, h4689, h4693, h4736, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4738 | h4738
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4739 | h4739
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4740 | h4740
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4741 | h4741
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4742 | h4742
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4743 | h4743
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4744 | h4744
                            · rcases h0bigk with h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [hlam, p4745_0]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h0, hlam, p4745_1]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h1951, hlam, p4745_0]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h2940, hlam, p4745_1]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h3280, hlam, p4745_1]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h0, h4736, h4741, hc01, hc23, hlam, hphi, ht12, p4745_1]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [hlam, p4745_0]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h3841, hlam, p4745_0]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h4487, hlam, p4745_1]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h0, h3280, h4736, h4741, hc01, hc23, hlam, hphi, ht12, p4745_1]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                rcases p4745_3 (m.d 0 1) (by simp) with h4756 | h4756
                                · linarith only [h1951, h4756, hlam]
                                · rcases p4745_3 (m.d 0 2) (by simp) with h4758 | h4758
                                  · linarith only [h3841, h4758, hlam]
                                  · linarith only [h0, h4758, hlam]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h4689, h4742, h4744, hc45, hlam, hphi, ht0b, ht5b, p4745_1, u0elo2]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [hlam, p4745_0]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h4487, h4689, h4742, h4744, hc45, hlam, hphi, ht0b, ht5b, p4745_1, u0elo2]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                rcases p4745_3 (m.d 0 1) (by simp) with h4764 | h4764
                                · linarith only [h1951, h4764, hlam]
                                · rcases p4745_3 (m.d 0 2) (by simp) with h4766 | h4766
                                  · linarith only [h3841, h4766, hlam]
                                  · linarith only [h4689, h4766, hlam]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                rcases p4745_3 (m.d 0 1) (by simp) with h4769 | h4769
                                · linarith only [h2940, h4769, hlam]
                                · rcases p4745_3 (m.d 0 2) (by simp) with h4771 | h4771
                                  · linarith only [h4487, h4771, hlam]
                                  · linarith only [h0, h4771, hlam]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h4689, h4742, h4744, hc45, hlam, hphi, ht0b, ht5b, p4745_1, u0elo3]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h4690, hlam, p4745_0]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [hlam, p4745_0]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                rcases p4745_3 (m.d 0 1) (by simp) with h4777 | h4777
                                · linarith only [h2940, h4777, hlam]
                                · rcases p4745_3 (m.d 0 2) (by simp) with h4779 | h4779
                                  · linarith only [h4487, h4779, hlam]
                                  · linarith only [h4689, h4779, hlam]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4745_1, u5elo0]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h4689, hlam, p4745_1]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h4691, hlam, p4745_0]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [h4692, hlam, p4745_1]
                              · have p4745_0 := h4745c.1
                                have p4745_1 := h4745c.2.1
                                have p4745_2 := h4745c.2.2.1
                                have p4745_3 := h4745c.2.2.2
                                linarith only [hlam, p4745_0]
                            · rcases h0bigk with h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [hlam, p4787_0]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h0, hlam, p4787_1]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h1951, hlam, p4787_0]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h2940, hlam, p4787_1]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h3280, hlam, p4787_1]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h0, h4736, h4741, hc01, hc23, hlam, hphi, ht12, p4787_1]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [hlam, p4787_0]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h3841, hlam, p4787_0]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h4487, hlam, p4787_1]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h0, h3280, h4736, h4741, hc01, hc23, hlam, hphi, ht12, p4787_1]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                rcases p4787_3 (m.d 0 1) (by simp) with h4798 | h4798
                                · linarith only [h1951, h4798, hlam]
                                · rcases p4787_3 (m.d 0 2) (by simp) with h4800 | h4800
                                  · linarith only [h3841, h4800, hlam]
                                  · linarith only [h0, h4800, hlam]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h4689, h4743, h4744, hc34, hlam, hphi, ht0b, ht45, ht5b, p4787_1, u0elo2]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [hlam, p4787_0]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h4487, h4689, h4743, h4744, hc34, hlam, hphi, ht0b, ht45, ht5b, p4787_1, u0elo2]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h4689, h4743, h4744, hc34, hlam, hphi, ht0b, ht45, ht5b, p4787_1, u0elo2]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                rcases p4787_3 (m.d 0 1) (by simp) with h4807 | h4807
                                · linarith only [h2940, h4807, hlam]
                                · rcases p4787_3 (m.d 0 2) (by simp) with h4809 | h4809
                                  · linarith only [h4487, h4809, hlam]
                                  · linarith only [h0, h4809, hlam]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h4689, h4743, h4744, hc34, hlam, hphi, ht0b, ht45, ht5b, p4787_1, u0elo3]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h4690, hlam, p4787_0]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [hlam, p4787_0]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h4689, h4690, h4743, h4744, hc34, hlam, hphi, ht0b, ht45, ht5b, p4787_1, u0elo2]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h0, h4689, h4736, h4741, h4743, h4744, hc01, hc23, hc34, hlam, hphi, ht12, ht45, p4787_1, u5elo0]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h4689, hlam, p4787_1]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h4691, hlam, p4787_0]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [h4692, hlam, p4787_1]
                              · have p4787_0 := h4787c.1
                                have p4787_1 := h4787c.2.1
                                have p4787_2 := h4787c.2.2.1
                                have p4787_3 := h4787c.2.2.2
                                linarith only [hlam, p4787_0]
                          · linarith only [h0, h4689, h4736, h4743, hc25, hlam, hphi, u5elo4]
                        · linarith only [h1951, h4693, h4742, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1951, h4690, h4693, h4741, hlam]
                    · linarith only [h1951, h4690, h4691, h4740, hc34, hlam, hphi, ht45, u5elo0]
                  · linarith only [h1951, h4690, h4739, hlam]
                · linarith only [h0, h4738, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h4487, h4689, h4692, hc25, hlam, hphi, u5elo4]
        · linarith only [h4487, h4689, h4690, h4691, hc25, hlam, hphi, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4829 | h4829
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4830 | h4830
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4831 | h4831
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4832 | h4832
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4833 | h4833
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4834 | h4834
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4835 | h4835
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4836 | h4836
                      · linarith only [h3841, h4689, h4690, h4831, h4836, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h3841, h4689, h4834, h4836, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h1951, h4829, h4835, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4840 | h4840
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4841 | h4841
                      · linarith only [h4831, h4834, h4841, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4843 | h4843
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4844 | h4844
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4845 | h4845
                            · rcases h0bigk with h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [hlam, p4846_0]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h0, hlam, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h1951, hlam, p4846_0]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h2940, hlam, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h3280, hlam, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h3841, h4831, h4834, hc01, hc34, hlam, hphi, ht12, ht23, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [hlam, p4846_0]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h3841, hlam, p4846_0]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h4487, hlam, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h3841, h4831, h4834, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h3841, h4831, h4834, hc01, hc34, hlam, hphi, ht12, ht23, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h3841, h4831, h4834, hc02, hc34, hlam, hphi, ht23, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [hlam, p4846_0]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h4690, hlam, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h3280, h3841, h4831, h4834, hc01, hc34, hlam, hphi, ht12, ht23, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h4487, h4832, hc01, hc12, hlam, hphi, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h4487, h4689, h4832, h4843, h4845, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h1951, h4487, h4832, hc01, hc12, hlam, hphi, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [hlam, p4846_0]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h3280, h4487, h4832, hc01, hc12, hlam, hphi, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4846_1, u5elo0]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h4689, hlam, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h4829, hlam, p4846_0]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [h4830, hlam, p4846_1]
                              · have p4846_0 := h4846c.1
                                have p4846_1 := h4846c.2.1
                                have p4846_2 := h4846c.2.2.1
                                have p4846_3 := h4846c.2.2.2
                                linarith only [hlam, p4846_0]
                            · linarith only [h3841, h4689, h4831, h4834, h4843, h4845, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h2940, h3841, h4487, h4689, h4830, h4831, h4834, h4844, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h3841, h4843, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1951, h4829, h4840, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h3841, h4689, h4833, hc12, hc23, hlam, hphi]
              · linarith only [h3841, h4831, h4832, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4878 | h4878
              · linarith only [h4487, h4689, h4831, h4878, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4880 | h4880
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4881 | h4881
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4882 | h4882
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4883 | h4883
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4884 | h4884
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4885 | h4885
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4886 | h4886
                            · rcases h0bigk with h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c | h4887c
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [hlam, p4887_0]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h0, hlam, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h1951, hlam, p4887_0]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h2940, hlam, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h3280, hlam, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h0, h4878, h4883, hc01, hc23, hlam, hphi, ht12, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [hlam, p4887_0]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h3841, hlam, p4887_0]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h4487, hlam, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h3280, h3841, h4690, h4831, h4881, hc01, hc23, hlam, hphi, ht12, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h4690, h4831, h4881, hc01, hc23, hlam, hphi, ht12, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h4690, h4831, h4881, hc02, hc23, hlam, hphi, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [hlam, p4887_0]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h4690, hlam, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h3280, h4690, h4831, h4881, hc01, hc23, hlam, hphi, ht12, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h4690, h4831, h4881, hc01, hc23, hlam, hphi, ht12, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h4689, h4884, h4886, hc45, hlam, hphi, ht0b, ht5b, p4887_1, u0elo3]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h1951, h4690, h4831, h4881, hc01, hc23, hlam, hphi, ht12, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [hlam, p4887_0]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h3280, h4690, h4831, h4881, hc01, hc23, hlam, hphi, ht12, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4887_1, u5elo0]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h4689, hlam, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h4829, hlam, p4887_0]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [h4830, hlam, p4887_1]
                              · have p4887_0 := h4887c.1
                                have p4887_1 := h4887c.2.1
                                have p4887_2 := h4887c.2.2.1
                                have p4887_3 := h4887c.2.2.2
                                linarith only [hlam, p4887_0]
                            · linarith only [h3841, h4690, h4886, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h4830, h4878, h4885, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                        · linarith only [h3841, h4690, h4831, h4881, h4884, hc02, hc35, hlam, hphi, ht23]
                      · linarith only [h4831, h4881, h4883, hlam]
                    · linarith only [h4690, h4829, h4881, h4882, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4918 | h4918
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4919 | h4919
                      · linarith only [h3280, h4831, h4880, h4881, h4919, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h3280, h4831, h4880, h4919, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h3280, h4829, h4831, h4880, h4918, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h4689, h4880, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h4487, h4689, h4830, hc25, hlam, hphi, u5elo4]
        · linarith only [h3841, h4689, h4829, hc25, hlam, hphi, u5elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4926 | h4926
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4927 | h4927
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4928 | h4928
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4929 | h4929
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4930 | h4930
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4931 | h4931
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4932 | h4932
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4933 | h4933
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4934 | h4934
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4935 | h4935
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4936 | h4936
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4937 | h4937
                            · rcases h0bigk with h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [hlam, p4938_0]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h0, hlam, p4938_1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h1951, hlam, p4938_0]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h2940, hlam, p4938_1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h3280, hlam, p4938_1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h4689, h4931, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4938_1, u5elo1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [hlam, p4938_0]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h3841, hlam, p4938_0]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h4487, hlam, p4938_1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h4689, hlam, p4938_0]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h3841, h4929, hc01, hc12, hlam, hphi, p4938_1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h0, h3841, h4929, hc01, hc12, hlam, hphi, p4938_1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [hlam, p4938_0]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h0, h3841, h4689, h4926, h4929, h4931, h4937, hc01, hc12, hc45, hlam, hphi, p4938_1, u5elo1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h0, h3841, h4689, h4929, hc01, hc12, hlam, hphi, p4938_1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h3841, h4926, h4929, hc01, hc12, hlam, hphi, p4938_1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h0, h3841, h4926, h4929, hc01, hc12, hlam, hphi, p4938_1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h4926, hlam, p4938_0]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [hlam, p4938_0]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h0, h3841, h4689, h4926, h4929, hc01, hc12, hlam, hphi, p4938_1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4938_1, u5elo0]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h0, h3280, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4938_1, u5elo1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h4927, hlam, p4938_0]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [h4928, hlam, p4938_1]
                              · have p4938_0 := h4938c.1
                                have p4938_1 := h4938c.2.1
                                have p4938_2 := h4938c.2.2.1
                                have p4938_3 := h4938c.2.2.2
                                linarith only [hlam, p4938_0]
                            · rcases h0bigk with h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c | h4964c
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [hlam, p4964_0]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h0, hlam, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h1951, hlam, p4964_0]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h2940, hlam, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h3280, hlam, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h3841, h4929, hc01, hc12, hlam, hphi, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [hlam, p4964_0]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h3841, hlam, p4964_0]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h4487, hlam, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h4689, hlam, p4964_0]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h3841, h4929, hc01, hc12, hlam, hphi, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h0, h3841, h4929, hc01, hc12, hlam, hphi, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [hlam, p4964_0]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h3841, h4928, h4929, h4937, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h3280, h3841, h4929, hc01, hc12, hlam, hphi, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h3841, h4926, h4929, hc01, hc12, hlam, hphi, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h0, h3841, h4926, h4929, hc01, hc12, hlam, hphi, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h4926, hlam, p4964_0]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [hlam, p4964_0]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h0, h3841, h4689, h4926, h4929, hc01, hc12, hlam, hphi, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4964_1, u5elo0]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h0, h3280, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4964_1, u5elo1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h4927, hlam, p4964_0]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [h4928, hlam, p4964_1]
                              · have p4964_0 := h4964c.1
                                have p4964_1 := h4964c.2.1
                                have p4964_2 := h4964c.2.2.1
                                have p4964_3 := h4964c.2.2.2
                                linarith only [hlam, p4964_0]
                          · linarith only [h0, h4487, h4936, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h3841, h4927, h4935, hlam]
                      · linarith only [h3841, h4926, h4934, hlam]
                    · linarith only [h3841, h4927, h4929, h4933, hlam]
                  · linarith only [h3841, h4926, h4929, h4932, hlam]
                · linarith only [h0, h4931, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h3841, h4929, h4930, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4997 | h4997
              · linarith only [h0, h4487, h4929, h4997, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4999 | h4999
                · linarith only [h0, h4689, h4929, h4999, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h4999, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5002 | h5002
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5003 | h5003
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5004 | h5004
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5005 | h5005
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5006 | h5006
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5007 | h5007
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5008 | h5008
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5009 | h5009
                          · linarith only [h0, h4487, h4928, h5003, h5009, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h4487, h5009, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h3841, h5008, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h3841, h4926, h5007, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1951, h4927, h5006, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                  · linarith only [h3841, h4926, h5002, h5005, hlam]
                · linarith only [h0, h5004, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h3841, h5002, h5003, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5018 | h5018
              · linarith only [h0, h4487, h5002, h5018, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5020 | h5020
                · linarith only [h0, h4689, h5002, h5020, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h5020, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h4926, h4927, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5024 | h5024
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5025 | h5025
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5026 | h5026
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5027 | h5027
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5028 | h5028
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5029 | h5029
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5030 | h5030
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5031 | h5031
                      · linarith only [h4926, h5024, h5026, h5031, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h3841, h5029, h5031, hc01, hc13, hlam, hphi]
                    · linarith only [h1951, h5024, h5030, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5035 | h5035
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5036 | h5036
                      · linarith only [h5026, h5029, h5036, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5038 | h5038
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5039 | h5039
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5040 | h5040
                            · rcases h0bigk with h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [hlam, p5041_0]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h0, hlam, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h1951, hlam, p5041_0]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h2940, hlam, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h3280, hlam, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h4689, h5028, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5041_1, u5elo1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [hlam, p5041_0]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h3841, hlam, p5041_0]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h4487, hlam, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h4689, hlam, p5041_0]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h3841, h5026, h5029, hc01, hc34, hlam, hphi, ht12, ht23, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h3841, h5026, h5029, hc02, hc34, hlam, hphi, ht23, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [hlam, p5041_0]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h4926, hlam, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h3280, h3841, h5026, h5029, hc01, hc34, hlam, hphi, ht12, ht23, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h4487, h5027, hc01, hc12, hlam, hphi, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h0, h4487, h5027, hc01, hc12, hlam, hphi, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h4487, h5024, h5027, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [hlam, p5041_0]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h0, h4487, h4689, h5027, hc01, hc12, hlam, hphi, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5041_1, u5elo0]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5041_1, u5elo0]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h5024, hlam, p5041_0]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [h5025, hlam, p5041_1]
                              · have p5041_0 := h5041c.1
                                have p5041_1 := h5041c.2.1
                                have p5041_2 := h5041c.2.2.1
                                have p5041_3 := h5041c.2.2.2
                                linarith only [hlam, p5041_0]
                            · linarith only [h5029, h5040, hc13, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h4487, h5025, h5039, hlam]
                        · linarith only [h0, h3841, h5038, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1951, h5024, h5035, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h4487, h5027, h5028, hc04, hlam, hphi, ht45, u5elo2]
              · linarith only [h0, h3841, h5026, h5027, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5073 | h5073
              · linarith only [h0, h4487, h5026, h5073, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5075 | h5075
                · linarith only [h0, h4689, h5026, h5075, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h5075, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h4926, h5024, h5025, hc35, hlam, hphi, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5079 | h5079
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5080 | h5080
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5081 | h5081
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5082 | h5082
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5083 | h5083
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5084 | h5084
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5085 | h5085
                      · linarith only [h1951, h4926, h5080, h5085, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h3841, h5083, h5085, hc01, hc13, hlam, hphi]
                    · linarith only [h5083, h5084, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5089 | h5089
                    · linarith only [h0, h3841, h5024, h5083, h5089, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1951, h5089, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h5082, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h3841, h5080, h5081, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5094 | h5094
              · linarith only [h0, h4487, h5080, h5094, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5096 | h5096
                · linarith only [h0, h4689, h5080, h5096, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h5096, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5099 | h5099
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5100 | h5100
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5101 | h5101
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5102 | h5102
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5103 | h5103
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5104 | h5104
                      · linarith only [h0, h3841, h4926, h5099, h5104, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h3841, h5102, h5104, hc01, hc13, hlam, hphi]
                    · linarith only [h5102, h5103, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5108 | h5108
                    · linarith only [h0, h3841, h5024, h5102, h5108, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1951, h5108, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h5101, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h3841, h5099, h5100, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5113 | h5113
              · linarith only [h0, h4487, h5099, h5113, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5115 | h5115
                · linarith only [h0, h4689, h5099, h5115, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h5115, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 6334000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1951 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2940 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3280 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3841 | h3841
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h1951 h2940 h3280 h3841
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h1951 h2940 h3280 h3841

set_option maxHeartbeats 6334000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1951 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2940 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h3280 | h3280
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h1951 h2940 h3280
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h1951 h2940 h3280

set_option maxHeartbeats 6334000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1951 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h2940 | h2940
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x0 m hb0 hb2 hb3 hb5 hg0 h1951 h2940
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x1 m hb0 hb2 hb3 hb5 hg0 h1951 h2940

set_option maxHeartbeats 6334000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1951 | h1951
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x0 m hb0 hb2 hb3 hb5 hg0 h1951
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1 m hb0 hb2 hb3 hb5 hg0 h1951

end R2N4
