import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_20S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5035 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5036 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5037 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h5038 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 1 2 3 (by decide) (by decide) with h5514 | h5514
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5515 | h5515
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5516 | h5516
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5517 | h5517
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5518 | h5518
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5519 | h5519
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5520 | h5520
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5521 | h5521
                · linarith only [h5035, h5038, h5521, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5523 | h5523
                  · linarith only [h5035, h5038, h5519, h5523, hlam]
                  · rcases h2bigk with h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h0, hlam, p5525_1]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5520, hc02, hc35, hlam, hphi, ht0b, ht5b, p5525_1]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      rcases p5525_3 (m.d 0 2) (by simp) with h5529 | h5529
                      · rcases p5525_3 (m.d 1 2) (by simp) with h5530 | h5530
                        · rcases p5525_3 (m.d 2 3) (by simp) with h5531 | h5531
                          · linarith only [h5034, h5531, hlam]
                          · linarith only [h5519, h5531, hlam]
                        · linarith only [h5515, h5530, hlam]
                      · linarith only [h5529, hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      rcases p5525_3 (m.d 0 2) (by simp) with h5536 | h5536
                      · rcases p5525_3 (m.d 1 2) (by simp) with h5537 | h5537
                        · rcases p5525_3 (m.d 2 3) (by simp) with h5538 | h5538
                          · linarith only [h5034, h5538, hlam]
                          · linarith only [h5520, h5538, hlam]
                        · linarith only [h5516, h5537, hlam]
                      · linarith only [h5536, hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5525_1]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5520, h5523, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5525_1]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      rcases p5525_3 (m.d 0 2) (by simp) with h5546 | h5546
                      · linarith only [h0, h5546, hlam]
                      · linarith only [h5035, h5546, hlam]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      rcases p5525_3 (m.d 0 2) (by simp) with h5549 | h5549
                      · linarith only [h0, h5549, hlam]
                      · linarith only [h5036, h5549, hlam]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5034, hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5514, hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5034, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p5525_1]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h0, h5034, h5520, h5523, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5525_1]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5035, hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5515, hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5519, hlam, p5525_1]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5521, hlam, p5525_1]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5036, hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5516, hlam, p5525_0]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h5520, hlam, p5525_1]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [h0, h5036, h5519, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5525_1]
                    · have p5525_0 := h5525c.1
                      have p5525_1 := h5525c.2.1
                      have p5525_2 := h5525c.2.2.1
                      have p5525_3 := h5525c.2.2.2
                      linarith only [hlam, p5525_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5567 | h5567
                · linarith only [h0, h3667, h5035, h5038, h5567, hc01, hc12, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5569 | h5569
                  · linarith only [h0, h3667, h5034, h5037, h5038, h5569, hc01, hc12, hlam, hphi]
                  · rcases h2bigk with h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h0, hlam, p5571_1]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h0, h5519, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5571_1]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      rcases p5571_3 (m.d 0 2) (by simp) with h5575 | h5575
                      · rcases p5571_3 (m.d 1 2) (by simp) with h5576 | h5576
                        · rcases p5571_3 (m.d 2 3) (by simp) with h5577 | h5577
                          · linarith only [h5034, h5577, hlam]
                          · linarith only [h5519, h5577, hlam]
                        · linarith only [h5515, h5576, hlam]
                      · linarith only [h5575, hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h0, h5519, h5520, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5571_1]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5571_1]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5519, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5571_1]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      rcases p5571_3 (m.d 0 2) (by simp) with h5586 | h5586
                      · linarith only [h0, h5586, hlam]
                      · linarith only [h5035, h5586, hlam]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5519, h5520, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5571_1]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5034, hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5514, hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5036, h5519, h5520, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5571_1]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5520, hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5035, hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5515, hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5519, hlam, p5571_1]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5567, hlam, p5571_1]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5036, hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5516, hlam, p5571_0]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5036, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5571_1]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [h5036, h5038, h5517, h5518, h5519, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5571_1]
                    · have p5571_0 := h5571c.1
                      have p5571_1 := h5571c.2.1
                      have p5571_2 := h5571c.2.2.1
                      have p5571_3 := h5571c.2.2.2
                      linarith only [hlam, p5571_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5605 | h5605
              · linarith only [h5037, h5038, h5514, h5517, h5518, h5519, h5605, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5607 | h5607
                · linarith only [h0, h5035, h5037, h5038, h5519, h5607, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5609 | h5609
                  · linarith only [h5037, h5038, h5609, hlam]
                  · rcases h2bigk with h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c | h5611c
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h0, hlam, p5611_1]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      rcases p5611_3 (m.d 0 2) (by simp) with h5614 | h5614
                      · rcases p5611_3 (m.d 1 2) (by simp) with h5615 | h5615
                        · rcases p5611_3 (m.d 2 3) (by simp) with h5616 | h5616
                          · linarith only [h5616, hlam, p5611_0]
                          · rcases p5611_3 (m.d 2 4) (by simp) with h5618 | h5618
                            · linarith only [h5035, h5618, hlam]
                            · linarith only [h5519, h5618, hlam]
                        · linarith only [h5514, h5615, hlam]
                      · linarith only [h5614, hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      rcases p5611_3 (m.d 0 2) (by simp) with h5623 | h5623
                      · rcases p5611_3 (m.d 1 2) (by simp) with h5624 | h5624
                        · rcases p5611_3 (m.d 2 3) (by simp) with h5625 | h5625
                          · linarith only [h5034, h5625, hlam]
                          · rcases p5611_3 (m.d 2 4) (by simp) with h5627 | h5627
                            · linarith only [h5627, hlam, p5611_0]
                            · rcases p5611_3 (m.d 2 5) (by simp) with h5629 | h5629
                              · linarith only [h5036, h5629, hlam]
                              · linarith only [h5607, h5629, hlam]
                        · linarith only [h5515, h5624, hlam]
                      · linarith only [h5623, hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      rcases p5611_3 (m.d 0 2) (by simp) with h5634 | h5634
                      · rcases p5611_3 (m.d 1 2) (by simp) with h5635 | h5635
                        · rcases p5611_3 (m.d 2 3) (by simp) with h5636 | h5636
                          · linarith only [h5034, h5636, hlam]
                          · rcases p5611_3 (m.d 2 4) (by simp) with h5638 | h5638
                            · linarith only [h5035, h5638, hlam]
                            · rcases p5611_3 (m.d 2 5) (by simp) with h5640 | h5640
                              · linarith only [h5640, hlam, p5611_0]
                              · rcases h4bigk with h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c | h5642c
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [hlam, p5642_0]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h3667, hlam, p5642_0]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5038, hc24, hc45, hlam, hphi, p5642_1]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5038, h5519, hc23, hc45, hlam, hphi, ht34, p5642_1]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5038, hlam, p5642_0]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  rcases p5642_3 (m.d 0 4) (by simp) with h5648 | h5648
                                  · linarith only [h3667, h5648, hlam]
                                  · rcases p5642_3 (m.d 1 4) (by simp) with h5650 | h5650
                                    · rcases p5642_3 (m.d 2 4) (by simp) with h5651 | h5651
                                      · linarith only [h5515, h5651, hlam]
                                      · rcases p5642_3 (m.d 3 4) (by simp) with h5653 | h5653
                                        · linarith only [h5517, h5653, hlam]
                                        · rcases p5642_3 (m.d 4 5) (by simp) with h5655 | h5655
                                          · linarith only [h5518, h5655, hlam]
                                          · linarith only [h5038, h5655, hlam]
                                    · linarith only [h3667, h5650, hlam]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [hlam, p5642_0]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  rcases p5642_3 (m.d 0 4) (by simp) with h5660 | h5660
                                  · linarith only [h3667, h5660, hlam]
                                  · linarith only [h5035, h5660, hlam]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  rcases p5642_3 (m.d 0 4) (by simp) with h5663 | h5663
                                  · linarith only [h3667, h5663, hlam]
                                  · linarith only [h5037, h5663, hlam]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h3667, h5038, hc01, hc14, hlam, hphi, p5642_1]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5035, hlam, p5642_1]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5515, hlam, p5642_1]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [hlam, p5642_0]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5519, hlam, p5642_1]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5607, hlam, p5642_0]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5037, hlam, p5642_1]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5517, hlam, p5642_0]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5037, h5038, hc24, hc45, hlam, hphi, p5642_1]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [hlam, p5642_0]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5609, hlam, p5642_0]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h3667, h5514, h5517, h5518, hc01, hc12, hlam, hphi, p5642_1]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5518, hlam, p5642_0]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  rcases p5642_3 (m.d 0 4) (by simp) with h5679 | h5679
                                  · linarith only [h5038, h5679, hlam]
                                  · linarith only [h5035, h5679, hlam]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [h5514, h5517, h5518, h5519, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5642_1]
                                · have p5642_0 := h5642c.1
                                  have p5642_1 := h5642c.2.1
                                  have p5642_2 := h5642c.2.2.1
                                  have p5642_3 := h5642c.2.2.2
                                  linarith only [hlam, p5642_0]
                        · linarith only [h5516, h5635, hlam]
                      · linarith only [h5634, hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5611_1]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      rcases p5611_3 (m.d 0 2) (by simp) with h5688 | h5688
                      · linarith only [h0, h5688, hlam]
                      · linarith only [h5034, h5688, hlam]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      rcases p5611_3 (m.d 0 2) (by simp) with h5691 | h5691
                      · linarith only [h0, h5691, hlam]
                      · linarith only [h5035, h5691, hlam]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      rcases p5611_3 (m.d 0 2) (by simp) with h5694 | h5694
                      · linarith only [h0, h5694, hlam]
                      · linarith only [h5036, h5694, hlam]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5034, hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5514, hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5519, hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5605, hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5035, hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5515, hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5611_1]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5607, hlam, p5611_1]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5036, hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5516, hlam, p5611_0]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5036, h5038, h5514, h5517, h5518, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5611_1]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [h5036, h5038, h5514, h5517, h5518, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5611_1]
                    · have p5611_0 := h5611c.1
                      have p5611_1 := h5611c.2.1
                      have p5611_2 := h5611c.2.2.1
                      have p5611_3 := h5611c.2.2.2
                      linarith only [hlam, p5611_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5712 | h5712
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5713 | h5713
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5714 | h5714
                · linarith only [h3667, h5518, h5714, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5716 | h5716
                  · linarith only [h3667, h5034, h5518, h5712, h5716, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases h2bigk with h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h0, hlam, p5718_1]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h0, h5713, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5718_1]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      rcases p5718_3 (m.d 0 2) (by simp) with h5722 | h5722
                      · rcases p5718_3 (m.d 1 2) (by simp) with h5723 | h5723
                        · rcases p5718_3 (m.d 2 3) (by simp) with h5724 | h5724
                          · linarith only [h5034, h5724, hlam]
                          · linarith only [h5712, h5724, hlam]
                        · linarith only [h5515, h5723, hlam]
                      · linarith only [h5722, hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      rcases p5718_3 (m.d 0 2) (by simp) with h5729 | h5729
                      · rcases p5718_3 (m.d 1 2) (by simp) with h5730 | h5730
                        · rcases p5718_3 (m.d 2 3) (by simp) with h5731 | h5731
                          · linarith only [h5034, h5731, hlam]
                          · linarith only [h5713, h5731, hlam]
                        · linarith only [h5516, h5730, hlam]
                      · linarith only [h5729, hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5718_1]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h5713, h5716, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5718_1]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      rcases p5718_3 (m.d 0 2) (by simp) with h5739 | h5739
                      · linarith only [h0, h5739, hlam]
                      · linarith only [h5035, h5739, hlam]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      rcases p5718_3 (m.d 0 2) (by simp) with h5742 | h5742
                      · linarith only [h0, h5742, hlam]
                      · linarith only [h5036, h5742, hlam]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h5034, hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h5514, hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h5034, h5712, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5718_1]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h0, h5034, h5712, h5714, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5718_1]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h5035, hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h5515, hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h5712, hlam, p5718_1]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h5714, hlam, p5718_1]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h5036, hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h5516, hlam, p5718_0]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h5713, hlam, p5718_1]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [h0, h5036, h5712, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5718_1]
                    · have p5718_0 := h5718c.1
                      have p5718_1 := h5718c.2.1
                      have p5718_2 := h5718c.2.2.1
                      have p5718_3 := h5718c.2.2.2
                      linarith only [hlam, p5718_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5760 | h5760
                · linarith only [h3667, h5518, h5760, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5762 | h5762
                  · linarith only [h3667, h5518, h5762, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases h2bigk with h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h0, hlam, p5764_1]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h0, h5712, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5764_1]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      rcases p5764_3 (m.d 0 2) (by simp) with h5768 | h5768
                      · rcases p5764_3 (m.d 1 2) (by simp) with h5769 | h5769
                        · rcases p5764_3 (m.d 2 3) (by simp) with h5770 | h5770
                          · linarith only [h5034, h5770, hlam]
                          · linarith only [h5712, h5770, hlam]
                        · linarith only [h5515, h5769, hlam]
                      · linarith only [h5768, hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h0, h5712, h5713, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5764_1]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5764_1]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5712, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5764_1]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      rcases p5764_3 (m.d 0 2) (by simp) with h5779 | h5779
                      · linarith only [h0, h5779, hlam]
                      · linarith only [h5035, h5779, hlam]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5712, h5713, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5764_1]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5034, hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5514, hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5036, h5712, h5713, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5764_1]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5713, hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5035, hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5515, hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5712, hlam, p5764_1]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5760, hlam, p5764_1]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5036, hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5516, hlam, p5764_0]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h5036, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5764_1]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [h0, h5036, h5712, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5764_1]
                    · have p5764_0 := h5764c.1
                      have p5764_1 := h5764c.2.1
                      have p5764_2 := h5764c.2.2.1
                      have p5764_3 := h5764c.2.2.2
                      linarith only [hlam, p5764_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5798 | h5798
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5799 | h5799
                · linarith only [h3667, h5037, h5518, h5712, h5798, h5799, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h5712, h5798, h5799, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5802 | h5802
                · linarith only [h3667, h5518, h5802, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5804 | h5804
                  · linarith only [h3667, h5037, h5518, h5804, hlam]
                  · rcases h2bigk with h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c | h5806c
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h0, hlam, p5806_1]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      rcases p5806_3 (m.d 0 2) (by simp) with h5809 | h5809
                      · rcases p5806_3 (m.d 1 2) (by simp) with h5810 | h5810
                        · rcases p5806_3 (m.d 2 3) (by simp) with h5811 | h5811
                          · linarith only [h5811, hlam, p5806_0]
                          · rcases p5806_3 (m.d 2 4) (by simp) with h5813 | h5813
                            · linarith only [h5035, h5813, hlam]
                            · linarith only [h5712, h5813, hlam]
                        · linarith only [h5514, h5810, hlam]
                      · linarith only [h5809, hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      rcases p5806_3 (m.d 0 2) (by simp) with h5818 | h5818
                      · rcases p5806_3 (m.d 1 2) (by simp) with h5819 | h5819
                        · rcases p5806_3 (m.d 2 3) (by simp) with h5820 | h5820
                          · linarith only [h5034, h5820, hlam]
                          · rcases p5806_3 (m.d 2 4) (by simp) with h5822 | h5822
                            · linarith only [h5822, hlam, p5806_0]
                            · rcases p5806_3 (m.d 2 5) (by simp) with h5824 | h5824
                              · linarith only [h5036, h5824, hlam]
                              · linarith only [h5802, h5824, hlam]
                        · linarith only [h5515, h5819, hlam]
                      · linarith only [h5818, hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      rcases p5806_3 (m.d 0 2) (by simp) with h5829 | h5829
                      · rcases p5806_3 (m.d 1 2) (by simp) with h5830 | h5830
                        · rcases p5806_3 (m.d 2 3) (by simp) with h5831 | h5831
                          · linarith only [h5034, h5831, hlam]
                          · rcases p5806_3 (m.d 2 4) (by simp) with h5833 | h5833
                            · linarith only [h5035, h5833, hlam]
                            · rcases p5806_3 (m.d 2 5) (by simp) with h5835 | h5835
                              · linarith only [h5835, hlam, p5806_0]
                              · rcases h4bigk with h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [hlam, p5837_0]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h3667, hlam, p5837_0]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h3667, h5518, hc24, hc45, hlam, hphi, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h3667, h5518, hc34, hc45, hlam, hphi, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5038, hlam, p5837_0]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5518, hc04, hc45, hlam, hphi, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [hlam, p5837_0]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5518, hc24, hc45, hlam, hphi, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5518, hc34, hc45, hlam, hphi, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5518, hlam, p5837_0]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5035, hlam, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5515, hlam, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [hlam, p5837_0]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5712, hlam, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5802, hlam, p5837_0]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5037, hlam, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5517, hlam, p5837_0]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h3667, h5037, h5518, hc24, hc45, hlam, hphi, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [hlam, p5837_0]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5804, hlam, p5837_0]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5037, h5712, hc23, hc45, hlam, hphi, ht34, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h3667, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  rcases p5837_3 (m.d 0 4) (by simp) with h5860 | h5860
                                  · linarith only [h5038, h5860, hlam]
                                  · linarith only [h5035, h5860, hlam]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [h5712, hc23, hc45, hlam, hphi, ht34, p5837_1]
                                · have p5837_0 := h5837c.1
                                  have p5837_1 := h5837c.2.1
                                  have p5837_2 := h5837c.2.2.1
                                  have p5837_3 := h5837c.2.2.2
                                  linarith only [hlam, p5837_0]
                        · linarith only [h5516, h5830, hlam]
                      · linarith only [h5829, hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5806_1]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      rcases p5806_3 (m.d 0 2) (by simp) with h5869 | h5869
                      · linarith only [h0, h5869, hlam]
                      · linarith only [h5034, h5869, hlam]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      rcases p5806_3 (m.d 0 2) (by simp) with h5872 | h5872
                      · linarith only [h0, h5872, hlam]
                      · linarith only [h5035, h5872, hlam]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      rcases p5806_3 (m.d 0 2) (by simp) with h5875 | h5875
                      · linarith only [h0, h5875, hlam]
                      · linarith only [h5036, h5875, hlam]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h5034, hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h5514, hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h5712, hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h5798, hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h5035, hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h5515, hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5806_1]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h5802, hlam, p5806_1]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h5036, hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h5516, hlam, p5806_0]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h5036, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5806_1]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [h0, h5036, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5806_1]
                    · have p5806_0 := h5806c.1
                      have p5806_1 := h5806c.2.1
                      have p5806_2 := h5806c.2.2.1
                      have p5806_3 := h5806c.2.2.2
                      linarith only [hlam, p5806_0]
        · linarith only [h3667, h5037, h5517, hlam]
      · linarith only [h0, h5036, h5516, hlam]
    · linarith only [h0, h5035, h5515, hlam]
  · linarith only [h0, h5034, h5514, hlam]

set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5035 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5036 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5037 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 0 4 5 (by decide) (by decide) with h5038 | h5038
  · exact r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg3667 h5034 h5035 h5036 h5037 h5038
  · exact r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg3667 h5034 h5035 h5036 h5037 h5038

end R2N4
