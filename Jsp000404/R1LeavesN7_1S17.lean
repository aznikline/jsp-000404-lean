import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S15
import Jsp000404.R1LeavesN7_1S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11673 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11675 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11677 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h11679 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 1 3 5 (by decide) (by decide) with h12504 | h12504
  · rcases m.htr 1 4 5 (by decide) (by decide) with h12505 | h12505
    · linarith only [h11679, h12504, h12505, h9965, h9967, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
    · linarith only [h11679, h12504, h12505, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h12508 | h12508
    · linarith only [h11679, h12508, h2, h9965, h9967, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h12510 | h12510
      · rcases m.htr 2 3 5 (by decide) (by decide) with h12511 | h12511
        · rcases m.htr 2 4 5 (by decide) (by decide) with h12512 | h12512
          · linarith only [h11673, h11679, h12512, h9965, h9967, hc12, hc24, hlam, hphi]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h12514 | h12514
            · linarith only [h12512, h12514, h7821, h9965, hc02, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h0bigk with h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c | h12516c
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                rcases p12516_3 (m.d 0 1) (by simp) with h12518 | h12518
                · rcases p12516_3 (m.d 0 2) (by simp) with h12519 | h12519
                  · linarith only [h0, h12519, hlam]
                  · rcases p12516_3 (m.d 0 3) (by simp) with h12521 | h12521
                    · linarith only [h1, h12521, hlam]
                    · linarith only [h12521, h4, hlam]
                · linarith only [h0, h12518, hlam]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h11679, h9965, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p12516_1]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                rcases p12516_3 (m.d 0 1) (by simp) with h12526 | h12526
                · rcases p12516_3 (m.d 0 2) (by simp) with h12527 | h12527
                  · linarith only [h0, h12527, hlam]
                  · rcases p12516_3 (m.d 0 3) (by simp) with h12529 | h12529
                    · linarith only [h1, h12529, hlam]
                    · linarith only [h12529, h9965, hlam]
                · linarith only [h12526, h2, hlam]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                rcases p12516_3 (m.d 0 1) (by simp) with h12533 | h12533
                · rcases p12516_3 (m.d 0 2) (by simp) with h12534 | h12534
                  · linarith only [h0, h12534, hlam]
                  · rcases p12516_3 (m.d 0 3) (by simp) with h12536 | h12536
                    · linarith only [h1, h12536, hlam]
                    · linarith only [h12536, h9966, hlam]
                · linarith only [h12533, h3, hlam]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h0, hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h4, hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h7821, hlam, p12516_1]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h9029, hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h1, hlam, p12516_1]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                rcases p12516_3 (m.d 0 1) (by simp) with h12546 | h12546
                · rcases p12516_3 (m.d 0 2) (by simp) with h12547 | h12547
                  · linarith only [h12547, h4, hlam]
                  · rcases p12516_3 (m.d 0 3) (by simp) with h12549 | h12549
                    · rcases p12516_3 (m.d 0 4) (by simp) with h12550 | h12550
                      · linarith only [h12550, h9965, hlam]
                      · linarith only [h12550, h7821, hlam]
                    · linarith only [h12549, h4, hlam]
                · linarith only [h0, h12546, hlam]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h11673, h11679, h4, h9965, hc12, hc23, hlam, hphi, p12516_1]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h11673, h11679, h12514, h4, h9966, hc12, hc23, hlam, hphi, p12516_1]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h2, hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h0, h12512, h7821, hc12, hc45, hlam, hphi, ht23, ht34, p12516_1]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h9965, hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h9967, hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h3, hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                rcases p12516_3 (m.d 0 1) (by simp) with h12564 | h12564
                · rcases p12516_3 (m.d 0 2) (by simp) with h12565 | h12565
                  · linarith only [h12565, h9029, hlam]
                  · rcases p12516_3 (m.d 0 3) (by simp) with h12567 | h12567
                    · rcases p12516_3 (m.d 0 4) (by simp) with h12568 | h12568
                      · linarith only [h12568, h9967, hlam]
                      · linarith only [h12568, h7821, hlam]
                    · linarith only [h12567, h4, hlam]
                · linarith only [h0, h12564, hlam]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h9966, hlam, p12516_0]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [h11673, h11679, h12512, h9029, h9965, hc12, hc45, hlam, hphi, ht23, ht34, p12516_1]
              · have p12516_0 := h12516c.1
                have p12516_1 := h12516c.2.1
                have p12516_2 := h12516c.2.2.1
                have p12516_3 := h12516c.2.2.2
                linarith only [hlam, p12516_0]
        · linarith only [h11673, h11679, h12511, h4, h9965, hc12, hc35, hlam, hphi, ht23]
      · linarith only [h12510, h4, h9965, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11673 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11675 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11677 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 1 3 4 (by decide) (by decide) with h11679 | h11679
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h11673 h11675 h11677 h11679
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h11673 h11675 h11677 h11679

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11673 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11675 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 1 2 5 (by decide) (by decide) with h11677 | h11677
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h11673 h11675 h11677
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h11673 h11675 h11677

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11673 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 1 2 4 (by decide) (by decide) with h11675 | h11675
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h11673 h11675
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h11673 h11675

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 1 2 3 (by decide) (by decide) with h11673 | h11673
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h11673
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h11673

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 0 4 5 (by decide) (by decide) with h9967 | h9967
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s14 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  rcases m.htr 0 3 5 (by decide) (by decide) with h9966 | h9966
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h7821 h9029 h9965 h9966
  · rcases m.htr 0 4 5 (by decide) (by decide) with h12578 | h12578
    · linarith only [h12578, h9965, h9966, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h12580 | h12580
      · linarith only [h0, h12580, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h12582 | h12582
        · linarith only [h0, h12582, h7821, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h12584 | h12584
          · linarith only [h0, h12584, h9029, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h12586 | h12586
            · rcases m.htr 1 3 5 (by decide) (by decide) with h12587 | h12587
              · linarith only [h1, h12587, h9966, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12589 | h12589
                · linarith only [h12578, h12589, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12591 | h12591
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12592 | h12592
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12593 | h12593
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12594 | h12594
                        · linarith only [h1, h12578, h12582, h12586, h12592, h12594, h2, h9966, hc12, hc25, hlam, hphi]
                        · rcases h0bigk with h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c | h12596c
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [hlam, p12596_0]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            rcases p12596_3 (m.d 0 1) (by simp) with h12598 | h12598
                            · rcases p12596_3 (m.d 0 2) (by simp) with h12599 | h12599
                              · linarith only [h0, h12599, hlam]
                              · rcases p12596_3 (m.d 0 3) (by simp) with h12601 | h12601
                                · linarith only [h1, h12601, hlam]
                                · linarith only [h12601, h4, hlam]
                            · linarith only [h0, h12598, hlam]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            rcases p12596_3 (m.d 0 1) (by simp) with h12605 | h12605
                            · rcases p12596_3 (m.d 0 2) (by simp) with h12606 | h12606
                              · linarith only [h0, h12606, hlam]
                              · rcases p12596_3 (m.d 0 3) (by simp) with h12608 | h12608
                                · linarith only [h1, h12608, hlam]
                                · rcases p12596_3 (m.d 0 4) (by simp) with h12610 | h12610
                                  · linarith only [h12610, h2, hlam]
                                  · rcases p12596_3 (m.d 0 5) (by simp) with h12612 | h12612
                                    · linarith only [h12612, h3, hlam]
                                    · linarith only [h12612, h9966, hlam]
                            · linarith only [h1, h12605, hlam]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            rcases p12596_3 (m.d 0 1) (by simp) with h12616 | h12616
                            · rcases p12596_3 (m.d 0 2) (by simp) with h12617 | h12617
                              · linarith only [h0, h12617, hlam]
                              · rcases p12596_3 (m.d 0 3) (by simp) with h12619 | h12619
                                · linarith only [h1, h12619, hlam]
                                · linarith only [h12619, h9965, hlam]
                            · linarith only [h12616, h2, hlam]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            rcases p12596_3 (m.d 0 1) (by simp) with h12623 | h12623
                            · rcases p12596_3 (m.d 0 2) (by simp) with h12624 | h12624
                              · linarith only [h0, h12624, hlam]
                              · rcases p12596_3 (m.d 0 3) (by simp) with h12626 | h12626
                                · linarith only [h1, h12626, hlam]
                                · rcases p12596_3 (m.d 0 4) (by simp) with h12628 | h12628
                                  · linarith only [h12628, h2, hlam]
                                  · rcases p12596_3 (m.d 0 5) (by simp) with h12630 | h12630
                                    · linarith only [h12630, h3, hlam]
                                    · rcases h2bigk with h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c | h12632c
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h4, hc12, hc23, hlam, hphi, p12632_1]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h4, hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h7821, hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h9029, hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h0, hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h12580, hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h12582, hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h12584, hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        rcases p12632_3 (m.d 0 2) (by simp) with h12643 | h12643
                                        · linarith only [h12643, hlam, p12632_0]
                                        · rcases p12632_3 (m.d 1 2) (by simp) with h12645 | h12645
                                          · linarith only [h12580, h12645, hlam]
                                          · rcases p12632_3 (m.d 2 3) (by simp) with h12647 | h12647
                                            · rcases p12632_3 (m.d 2 4) (by simp) with h12648 | h12648
                                              · linarith only [h12591, h12648, hlam]
                                              · linarith only [h12648, h7821, hlam]
                                            · linarith only [h12647, hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        rcases p12632_3 (m.d 0 2) (by simp) with h12652 | h12652
                                        · linarith only [h12652, h4, hlam]
                                        · linarith only [h0, h12652, hlam]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h1, h12586, h12593, h12594, h9966, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12632_1]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h9029, hc02, hc23, hlam, hphi, p12632_1]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        rcases p12632_3 (m.d 0 2) (by simp) with h12658 | h12658
                                        · linarith only [h12658, hlam, p12632_0]
                                        · rcases p12632_3 (m.d 1 2) (by simp) with h12660 | h12660
                                          · linarith only [h12582, h12660, hlam]
                                          · rcases p12632_3 (m.d 2 3) (by simp) with h12662 | h12662
                                            · rcases p12632_3 (m.d 2 4) (by simp) with h12663 | h12663
                                              · rcases p12632_3 (m.d 2 5) (by simp) with h12664 | h12664
                                                · linarith only [h12593, h12664, hlam]
                                                · linarith only [h12664, h9029, hlam]
                                              · linarith only [h12663, hlam, p12632_0]
                                            · linarith only [h12662, h4, hlam]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        rcases p12632_3 (m.d 0 2) (by simp) with h12669 | h12669
                                        · linarith only [h12669, h7821, hlam]
                                        · linarith only [h0, h12669, hlam]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h12591, hlam, p12632_1]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h1, h12586, h12593, h12594, h9966, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12632_1]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        rcases p12632_3 (m.d 0 2) (by simp) with h12675 | h12675
                                        · linarith only [h12675, hlam, p12632_0]
                                        · rcases p12632_3 (m.d 1 2) (by simp) with h12677 | h12677
                                          · linarith only [h12584, h12677, hlam]
                                          · rcases p12632_3 (m.d 2 3) (by simp) with h12679 | h12679
                                            · rcases p12632_3 (m.d 2 4) (by simp) with h12680 | h12680
                                              · rcases p12632_3 (m.d 2 5) (by simp) with h12681 | h12681
                                                · rcases h3bigk with h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c | h12682c
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [hlam, p12682_0]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h12586, h9966, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p12682_1]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h4, hlam, p12682_1]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h12594, h9966, hc34, hc45, hlam, hphi, p12682_1]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h9966, hlam, p12682_0]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h1, hlam, p12682_0]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [hlam, p12682_0]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h12580, hlam, p12682_1]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h1, h12594, h9966, hc34, hc45, hlam, hphi, p12682_1]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h12587, hlam, p12682_0]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    rcases p12682_3 (m.d 0 3) (by simp) with h12693 | h12693
                                                    · linarith only [h12693, h4, hlam]
                                                    · rcases p12682_3 (m.d 1 3) (by simp) with h12695 | h12695
                                                      · linarith only [h12580, h12695, hlam]
                                                      · rcases p12682_3 (m.d 2 3) (by simp) with h12697 | h12697
                                                        · rcases p12682_3 (m.d 3 4) (by simp) with h12698 | h12698
                                                          · linarith only [h12591, h12698, hlam]
                                                          · rcases p12682_3 (m.d 3 5) (by simp) with h12700 | h12700
                                                            · linarith only [h12592, h12700, hlam]
                                                            · linarith only [h12700, h9966, hlam]
                                                        · linarith only [h12697, h4, hlam]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    rcases p12682_3 (m.d 0 3) (by simp) with h12704 | h12704
                                                    · linarith only [h12704, h4, hlam]
                                                    · linarith only [h1, h12704, hlam]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [hlam, p12682_0]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h1, h12586, h12591, h12593, h12594, h9966, hlam, p12682_2]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h1, h12586, h9966, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12682_1]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h9965, hlam, p12682_0]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h12586, hlam, p12682_0]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h12591, hlam, p12682_0]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [hlam, p12682_0]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h12594, hlam, p12682_1]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h1, h12586, h12592, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12682_1]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h12586, h12592, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12682_1]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [h12592, hlam, p12682_0]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    rcases p12682_3 (m.d 0 3) (by simp) with h12718 | h12718
                                                    · linarith only [h12718, h9966, hlam]
                                                    · linarith only [h12718, h9965, hlam]
                                                  · have p12682_0 := h12682c.1
                                                    have p12682_1 := h12682c.2.1
                                                    have p12682_2 := h12682c.2.2.1
                                                    have p12682_3 := h12682c.2.2.2
                                                    linarith only [hlam, p12682_0]
                                                · linarith only [h12681, hlam, p12632_0]
                                              · linarith only [h12680, h7821, hlam]
                                            · linarith only [h12679, h4, hlam]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        rcases p12632_3 (m.d 0 2) (by simp) with h12725 | h12725
                                        · linarith only [h12725, h9029, hlam]
                                        · linarith only [h0, h12725, hlam]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h12592, hlam, p12632_1]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [h12593, hlam, p12632_0]
                                      · have p12632_0 := h12632c.1
                                        have p12632_1 := h12632c.2.1
                                        have p12632_2 := h12632c.2.2.1
                                        have p12632_3 := h12632c.2.2.2
                                        linarith only [hlam, p12632_0]
                            · linarith only [h12623, h3, hlam]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h0, hlam, p12596_0]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [hlam, p12596_0]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h4, hlam, p12596_0]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h7821, hlam, p12596_1]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h9029, hlam, p12596_0]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h1, hlam, p12596_1]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h0, h12591, h12593, h12594, h9966, hc12, hc23, hlam, hphi, p12596_1]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [hlam, p12596_0]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h12582, h12591, h12593, h12594, h2, h9966, hc12, hc23, hlam, hphi, p12596_1]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h9966, hlam, p12596_1]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h2, hlam, p12596_0]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h0, h12591, h12593, h12594, h9965, h9966, hc12, hc23, hlam, hphi, p12596_1]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h9965, hlam, p12596_0]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [hlam, p12596_0]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h12578, hlam, p12596_0]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h3, hlam, p12596_0]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h0, h12591, h12593, h12594, h9966, hc12, hc23, hlam, hphi, p12596_1]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h1, h12586, h12591, h12593, h12594, h9966, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12596_1]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [h12582, h12591, h12593, h12594, h2, h9966, hc12, hc23, hlam, hphi, p12596_1]
                          · have p12596_0 := h12596c.1
                            have p12596_1 := h12596c.2.1
                            have p12596_2 := h12596c.2.2.1
                            have p12596_3 := h12596c.2.2.2
                            linarith only [hlam, p12596_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12752 | h12752
                        · linarith only [h1, h12586, h12593, h12752, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c | h12754c
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [hlam, p12754_0]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            rcases p12754_3 (m.d 0 1) (by simp) with h12756 | h12756
                            · rcases p12754_3 (m.d 0 2) (by simp) with h12757 | h12757
                              · linarith only [h0, h12757, hlam]
                              · rcases p12754_3 (m.d 0 3) (by simp) with h12759 | h12759
                                · linarith only [h1, h12759, hlam]
                                · linarith only [h12759, h4, hlam]
                            · linarith only [h0, h12756, hlam]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            rcases p12754_3 (m.d 0 1) (by simp) with h12763 | h12763
                            · rcases p12754_3 (m.d 0 2) (by simp) with h12764 | h12764
                              · linarith only [h0, h12764, hlam]
                              · rcases p12754_3 (m.d 0 3) (by simp) with h12766 | h12766
                                · linarith only [h1, h12766, hlam]
                                · rcases p12754_3 (m.d 0 4) (by simp) with h12768 | h12768
                                  · linarith only [h12768, h2, hlam]
                                  · rcases p12754_3 (m.d 0 5) (by simp) with h12770 | h12770
                                    · linarith only [h12770, h3, hlam]
                                    · linarith only [h12770, h9966, hlam]
                            · linarith only [h1, h12763, hlam]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            rcases p12754_3 (m.d 0 1) (by simp) with h12774 | h12774
                            · rcases p12754_3 (m.d 0 2) (by simp) with h12775 | h12775
                              · linarith only [h0, h12775, hlam]
                              · rcases p12754_3 (m.d 0 3) (by simp) with h12777 | h12777
                                · linarith only [h1, h12777, hlam]
                                · linarith only [h12777, h9965, hlam]
                            · linarith only [h12774, h2, hlam]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            rcases p12754_3 (m.d 0 1) (by simp) with h12781 | h12781
                            · rcases p12754_3 (m.d 0 2) (by simp) with h12782 | h12782
                              · linarith only [h0, h12782, hlam]
                              · rcases p12754_3 (m.d 0 3) (by simp) with h12784 | h12784
                                · linarith only [h1, h12784, hlam]
                                · rcases p12754_3 (m.d 0 4) (by simp) with h12786 | h12786
                                  · linarith only [h12786, h2, hlam]
                                  · rcases p12754_3 (m.d 0 5) (by simp) with h12788 | h12788
                                    · linarith only [h12788, h3, hlam]
                                    · rcases h2bigk with h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c | h12790c
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h7821, hc12, hc24, hlam, hphi, p12790_1]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h4, hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h7821, hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h9029, hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h0, hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h12580, hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h12582, hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h12584, hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        rcases p12790_3 (m.d 0 2) (by simp) with h12801 | h12801
                                        · linarith only [h12801, hlam, p12790_0]
                                        · rcases p12790_3 (m.d 1 2) (by simp) with h12803 | h12803
                                          · linarith only [h12580, h12803, hlam]
                                          · rcases p12790_3 (m.d 2 3) (by simp) with h12805 | h12805
                                            · rcases p12790_3 (m.d 2 4) (by simp) with h12806 | h12806
                                              · linarith only [h12591, h12806, hlam]
                                              · linarith only [h12806, h7821, hlam]
                                            · linarith only [h12805, hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        rcases p12790_3 (m.d 0 2) (by simp) with h12810 | h12810
                                        · linarith only [h12810, h4, hlam]
                                        · linarith only [h0, h12810, hlam]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h7821, hc02, hc23, hlam, hphi, p12790_1]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h1, h12586, h12592, h9966, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12790_1]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h0, h12593, hc12, hc45, hlam, hphi, ht23, ht34, p12790_1]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h12593, hc12, hc45, hlam, hphi, ht23, ht34, p12790_1]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h12591, hlam, p12790_1]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [hlam, p12790_0]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h12593, hlam, p12790_1]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        rcases p12790_3 (m.d 0 2) (by simp) with h12821 | h12821
                                        · linarith only [h12821, hlam, p12790_0]
                                        · rcases p12790_3 (m.d 1 2) (by simp) with h12823 | h12823
                                          · linarith only [h12584, h12823, hlam]
                                          · rcases p12790_3 (m.d 2 3) (by simp) with h12825 | h12825
                                            · rcases p12790_3 (m.d 2 4) (by simp) with h12826 | h12826
                                              · linarith only [h12593, h12826, hlam]
                                              · linarith only [h12826, h7821, hlam]
                                            · linarith only [h12825, h4, hlam]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        rcases p12790_3 (m.d 0 2) (by simp) with h12830 | h12830
                                        · linarith only [h12830, h9029, hlam]
                                        · linarith only [h0, h12830, hlam]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h12592, hlam, p12790_1]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [h0, h7821, hc12, hc25, hlam, hphi, p12790_1]
                                      · have p12790_0 := h12790c.1
                                        have p12790_1 := h12790c.2.1
                                        have p12790_2 := h12790c.2.2.1
                                        have p12790_3 := h12790c.2.2.2
                                        linarith only [hlam, p12790_0]
                            · linarith only [h12781, h3, hlam]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h0, hlam, p12754_0]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [hlam, p12754_0]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h4, hlam, p12754_0]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h7821, hlam, p12754_1]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h9029, hlam, p12754_0]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h1, hlam, p12754_1]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h0, h9966, hc12, hc35, hlam, hphi, ht23, p12754_1]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [hlam, p12754_0]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h0, h7821, h9966, hc12, hc35, hlam, hphi, ht23, p12754_1]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h9966, hlam, p12754_1]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h2, hlam, p12754_0]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h0, h9965, h9966, hc12, hc35, hlam, hphi, ht23, p12754_1]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h9965, hlam, p12754_0]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [hlam, p12754_0]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h12578, hlam, p12754_0]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h3, hlam, p12754_0]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h0, h12592, h9966, hc12, hc23, hlam, hphi, p12754_1]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h1, h12586, h12592, h9966, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12754_1]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [h12582, h12592, h2, h9966, hc12, hc23, hlam, hphi, p12754_1]
                          · have p12754_0 := h12754c.1
                            have p12754_1 := h12754c.2.1
                            have p12754_2 := h12754c.2.2.1
                            have p12754_3 := h12754c.2.2.2
                            linarith only [hlam, p12754_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12857 | h12857
                      · linarith only [h12578, h12582, h12591, h12592, h12857, h2, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12859 | h12859
                        · linarith only [h0, h1, h12586, h12857, h12859, h7821, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h0bigk with h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c | h12861c
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [hlam, p12861_0]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            rcases p12861_3 (m.d 0 1) (by simp) with h12863 | h12863
                            · rcases p12861_3 (m.d 0 2) (by simp) with h12864 | h12864
                              · linarith only [h0, h12864, hlam]
                              · rcases p12861_3 (m.d 0 3) (by simp) with h12866 | h12866
                                · linarith only [h1, h12866, hlam]
                                · linarith only [h12866, h4, hlam]
                            · linarith only [h0, h12863, hlam]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            rcases p12861_3 (m.d 0 1) (by simp) with h12870 | h12870
                            · rcases p12861_3 (m.d 0 2) (by simp) with h12871 | h12871
                              · linarith only [h0, h12871, hlam]
                              · rcases p12861_3 (m.d 0 3) (by simp) with h12873 | h12873
                                · linarith only [h1, h12873, hlam]
                                · rcases p12861_3 (m.d 0 4) (by simp) with h12875 | h12875
                                  · linarith only [h12875, h2, hlam]
                                  · rcases p12861_3 (m.d 0 5) (by simp) with h12877 | h12877
                                    · linarith only [h12877, h3, hlam]
                                    · linarith only [h12877, h9966, hlam]
                            · linarith only [h1, h12870, hlam]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            rcases p12861_3 (m.d 0 1) (by simp) with h12881 | h12881
                            · rcases p12861_3 (m.d 0 2) (by simp) with h12882 | h12882
                              · linarith only [h0, h12882, hlam]
                              · rcases p12861_3 (m.d 0 3) (by simp) with h12884 | h12884
                                · linarith only [h1, h12884, hlam]
                                · linarith only [h12884, h9965, hlam]
                            · linarith only [h12881, h2, hlam]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            rcases p12861_3 (m.d 0 1) (by simp) with h12888 | h12888
                            · rcases p12861_3 (m.d 0 2) (by simp) with h12889 | h12889
                              · linarith only [h0, h12889, hlam]
                              · rcases p12861_3 (m.d 0 3) (by simp) with h12891 | h12891
                                · linarith only [h1, h12891, hlam]
                                · rcases p12861_3 (m.d 0 4) (by simp) with h12893 | h12893
                                  · linarith only [h12893, h2, hlam]
                                  · rcases p12861_3 (m.d 0 5) (by simp) with h12895 | h12895
                                    · linarith only [h12895, h3, hlam]
                                    · rcases h2bigk with h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c | h12897c
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h7821, hc12, hc24, hlam, hphi, p12897_1]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h4, hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h7821, hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h9029, hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h0, hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h12580, hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h12582, hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h12584, hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h12592, h12859, hc02, hc45, hlam, hphi, ht23, ht34, p12897_1]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h12592, h12859, hc12, hc45, hlam, hphi, ht23, ht34, p12897_1]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h12592, h12859, hc24, hc45, hlam, hphi, p12897_1]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h12592, hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h0, h12591, h12592, h12859, hc12, hc45, hlam, hphi, ht23, ht34, p12897_1]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h12591, h12592, h12859, hc12, hc45, hlam, hphi, ht23, ht34, p12897_1]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h12591, hlam, p12897_1]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [hlam, p12897_0]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h12857, hlam, p12897_1]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        rcases p12897_3 (m.d 0 2) (by simp) with h12918 | h12918
                                        · linarith only [h12918, hlam, p12897_0]
                                        · rcases p12897_3 (m.d 1 2) (by simp) with h12920 | h12920
                                          · linarith only [h12584, h12920, hlam]
                                          · rcases p12897_3 (m.d 2 3) (by simp) with h12922 | h12922
                                            · linarith only [h12592, h12922, hlam]
                                            · linarith only [h12922, h4, hlam]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        rcases p12897_3 (m.d 0 2) (by simp) with h12925 | h12925
                                        · linarith only [h12925, h9029, hlam]
                                        · linarith only [h0, h12925, hlam]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h0, h12592, h12859, h4, hc12, hc45, hlam, hphi, ht23, ht34, p12897_1]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [h0, h12592, h12859, h7821, hc12, hc45, hlam, hphi, ht23, ht34, p12897_1]
                                      · have p12897_0 := h12897c.1
                                        have p12897_1 := h12897c.2.1
                                        have p12897_2 := h12897c.2.2.1
                                        have p12897_3 := h12897c.2.2.2
                                        linarith only [hlam, p12897_0]
                            · linarith only [h12888, h3, hlam]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h0, hlam, p12861_0]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [hlam, p12861_0]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h4, hlam, p12861_0]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h7821, hlam, p12861_1]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h9029, hlam, p12861_0]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h1, hlam, p12861_1]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h0, h12859, h9966, hc12, hc45, hlam, hphi, ht23, ht34, p12861_1]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [hlam, p12861_0]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h0, h12859, h7821, h9966, hc12, hc45, hlam, hphi, ht23, ht34, p12861_1]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h9966, hlam, p12861_1]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h2, hlam, p12861_0]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h0, h12859, h9965, h9966, hc12, hc45, hlam, hphi, ht23, ht34, p12861_1]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h9965, hlam, p12861_0]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [hlam, p12861_0]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h12578, hlam, p12861_0]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h3, hlam, p12861_0]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            rcases p12861_3 (m.d 0 1) (by simp) with h12948 | h12948
                            · rcases p12861_3 (m.d 0 2) (by simp) with h12949 | h12949
                              · linarith only [h12949, h9029, hlam]
                              · rcases p12861_3 (m.d 0 3) (by simp) with h12951 | h12951
                                · linarith only [h12951, h9966, hlam]
                                · linarith only [h12951, h4, hlam]
                            · linarith only [h0, h12948, hlam]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [h1, h12586, h12592, h12859, h9029, hc34, hc45, hlam, hphi, p12861_1]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            rcases p12861_3 (m.d 0 1) (by simp) with h12956 | h12956
                            · rcases p12861_3 (m.d 0 2) (by simp) with h12957 | h12957
                              · linarith only [h12957, h9029, hlam]
                              · rcases p12861_3 (m.d 0 3) (by simp) with h12959 | h12959
                                · linarith only [h12959, h9966, hlam]
                                · linarith only [h12959, h9965, hlam]
                            · linarith only [h12956, h2, hlam]
                          · have p12861_0 := h12861c.1
                            have p12861_1 := h12861c.2.1
                            have p12861_2 := h12861c.2.2.1
                            have p12861_3 := h12861c.2.2.2
                            linarith only [hlam, p12861_0]
                  · linarith only [h0, h1, h12586, h12591, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h12586, h9965, h9966, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 8178000 in
set_option maxHeartbeats 8178000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s13_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h7821 := hg7821
  have h9029 := hg9029
  exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s14 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h7821 h9029 h9965

end R2N4
