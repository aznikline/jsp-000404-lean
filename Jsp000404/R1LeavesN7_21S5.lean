import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S3
import Jsp000404.R1LeavesN7_21S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5714000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_25_L_0_L_I_H_I_s0_x0 m hb0 hb2 hb5 hg0 h1
  · exact r1l7_10_12_25_L_0_L_I_H_I_s0_x1 m hb0 hb2 hb5 hg0 h1

set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4554 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4555 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4556 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 4 5 (by decide) (by decide) with h4557 | h4557
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4558 | h4558
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4559 | h4559
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4560 | h4560
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4561 | h4561
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4562 | h4562
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4563 | h4563
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4564 | h4564
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4565 | h4565
                  · linarith only [h4553, h4562, h4565, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h4553, h4562, h4564, h4565, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4568 | h4568
                  · linarith only [h4553, h4562, h4564, h4568, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases h2bigk with h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h0, hlam, p4570_1]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4563, hc35, hlam, hphi, ht0b, ht5b, p4570_1, u0elo1]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      rcases p4570_3 (m.d 0 2) (by simp) with h4574 | h4574
                      · rcases p4570_3 (m.d 1 2) (by simp) with h4575 | h4575
                        · rcases p4570_3 (m.d 2 3) (by simp) with h4576 | h4576
                          · linarith only [h4553, h4576, hlam]
                          · linarith only [h4562, h4576, hlam]
                        · linarith only [h4559, h4575, hlam]
                      · linarith only [h4574, hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      rcases p4570_3 (m.d 0 2) (by simp) with h4581 | h4581
                      · rcases p4570_3 (m.d 1 2) (by simp) with h4582 | h4582
                        · rcases p4570_3 (m.d 2 3) (by simp) with h4583 | h4583
                          · linarith only [h4553, h4583, hlam]
                          · linarith only [h4563, h4583, hlam]
                        · linarith only [h4560, h4582, hlam]
                      · linarith only [h4581, hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4553, h4563, h4568, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4570_1]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      rcases p4570_3 (m.d 0 2) (by simp) with h4590 | h4590
                      · linarith only [h0, h4590, hlam]
                      · linarith only [h4553, h4590, hlam]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      rcases p4570_3 (m.d 0 2) (by simp) with h4593 | h4593
                      · linarith only [h0, h4593, hlam]
                      · linarith only [h4554, h4593, hlam]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      rcases p4570_3 (m.d 0 2) (by simp) with h4596 | h4596
                      · linarith only [h0, h4596, hlam]
                      · linarith only [h4555, h4596, hlam]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4553, hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4558, hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4553, h4562, hc34, hlam, hphi, ht0b, ht45, ht5b, p4570_1, u0elo1]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4553, h4563, h4568, hc34, hlam, hphi, ht0b, ht45, ht5b, p4570_1, u0elo1]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4554, hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4559, hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4562, hlam, p4570_1]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4564, hlam, p4570_1]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4555, hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4560, hlam, p4570_0]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4563, hlam, p4570_1]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [h4555, h4562, hc34, hlam, hphi, ht0b, ht45, ht5b, p4570_1, u0elo1]
                    · have p4570_0 := h4570c.1
                      have p4570_1 := h4570c.2.1
                      have p4570_2 := h4570c.2.2.1
                      have p4570_3 := h4570c.2.2.2
                      linarith only [hlam, p4570_0]
              · linarith only [h4553, h4556, h4562, h4563, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4615 | h4615
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4616 | h4616
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4617 | h4617
                  · rcases h2bigk with h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h0, hlam, p4618_1]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4615, h4617, hc45, hlam, hphi, ht0b, ht5b, p4618_1, u0elo1]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4562, h4615, h4617, hc45, hlam, hphi, ht0b, ht5b, p4618_1, u0elo1]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      rcases p4618_3 (m.d 0 2) (by simp) with h4623 | h4623
                      · rcases p4618_3 (m.d 1 2) (by simp) with h4624 | h4624
                        · rcases p4618_3 (m.d 2 3) (by simp) with h4625 | h4625
                          · linarith only [h4553, h4625, hlam]
                          · linarith only [h4615, h4625, hlam]
                        · linarith only [h4560, h4624, hlam]
                      · linarith only [h4623, hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4553, h4615, h4617, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4618_1]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      rcases p4618_3 (m.d 0 2) (by simp) with h4632 | h4632
                      · linarith only [h0, h4632, hlam]
                      · linarith only [h4553, h4632, hlam]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      rcases p4618_3 (m.d 0 2) (by simp) with h4635 | h4635
                      · linarith only [h0, h4635, hlam]
                      · linarith only [h4554, h4635, hlam]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      rcases p4618_3 (m.d 0 2) (by simp) with h4638 | h4638
                      · linarith only [h0, h4638, hlam]
                      · linarith only [h4555, h4638, hlam]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4553, hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4558, hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4562, hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4554, h4562, h4615, h4617, hc45, hlam, hphi, ht0b, ht5b, p4618_1, u0elo1]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4554, hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4559, hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4554, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4618_1, u0elo1]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4554, h4615, h4617, hc45, hlam, hphi, ht0b, ht5b, p4618_1, u0elo1]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4555, hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4560, hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4615, hlam, p4618_1]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [h4616, hlam, p4618_0]
                    · have p4618_0 := h4618c.1
                      have p4618_1 := h4618c.2.1
                      have p4618_2 := h4618c.2.2.1
                      have p4618_3 := h4618c.2.2.2
                      linarith only [hlam, p4618_0]
                  · linarith only [h4557, h4562, h4617, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h4554, h4557, h4562, h4615, h4616, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4658 | h4658
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4659 | h4659
                  · rcases h2bigk with h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h0, hlam, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      rcases p4660_3 (m.d 0 2) (by simp) with h4663 | h4663
                      · rcases p4660_3 (m.d 1 2) (by simp) with h4664 | h4664
                        · rcases p4660_3 (m.d 2 3) (by simp) with h4665 | h4665
                          · linarith only [h4665, hlam, p4660_0]
                          · rcases p4660_3 (m.d 2 4) (by simp) with h4667 | h4667
                            · linarith only [h4554, h4667, hlam]
                            · linarith only [h4562, h4667, hlam]
                        · linarith only [h4558, h4664, hlam]
                      · linarith only [h4663, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4658, hc45, hlam, hphi, ht0b, ht5b, p4660_1, u0elo1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      rcases p4660_3 (m.d 0 2) (by simp) with h4673 | h4673
                      · rcases p4660_3 (m.d 1 2) (by simp) with h4674 | h4674
                        · rcases p4660_3 (m.d 2 3) (by simp) with h4675 | h4675
                          · linarith only [h4553, h4675, hlam]
                          · rcases p4660_3 (m.d 2 4) (by simp) with h4677 | h4677
                            · linarith only [h4554, h4677, hlam]
                            · linarith only [h4658, h4677, hlam]
                        · linarith only [h4560, h4674, hlam]
                      · linarith only [h4673, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4554, h4658, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      rcases p4660_3 (m.d 0 2) (by simp) with h4684 | h4684
                      · linarith only [h0, h4684, hlam]
                      · linarith only [h4553, h4684, hlam]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      rcases p4660_3 (m.d 0 2) (by simp) with h4687 | h4687
                      · linarith only [h0, h4687, hlam]
                      · linarith only [h4554, h4687, hlam]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      rcases p4660_3 (m.d 0 2) (by simp) with h4690 | h4690
                      · linarith only [h0, h4690, hlam]
                      · linarith only [h4555, h4690, hlam]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4553, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4558, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4562, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4615, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4554, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4559, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4554, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4660_1, u0elo1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4554, h4615, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4660_1, u0elo1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4555, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4560, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4660_1, u0elo1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4658, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [hlam, p4660_0]
                  · linarith only [h4554, h4557, h4562, h4659, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4709 | h4709
                  · rcases h2bigk with h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h0, hlam, p4710_1]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      rcases p4710_3 (m.d 0 2) (by simp) with h4713 | h4713
                      · rcases p4710_3 (m.d 1 2) (by simp) with h4714 | h4714
                        · rcases p4710_3 (m.d 2 3) (by simp) with h4715 | h4715
                          · linarith only [h4715, hlam, p4710_0]
                          · rcases p4710_3 (m.d 2 4) (by simp) with h4717 | h4717
                            · linarith only [h4554, h4717, hlam]
                            · linarith only [h4562, h4717, hlam]
                        · linarith only [h4558, h4714, hlam]
                      · linarith only [h4713, hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      rcases p4710_3 (m.d 0 2) (by simp) with h4722 | h4722
                      · rcases p4710_3 (m.d 1 2) (by simp) with h4723 | h4723
                        · rcases p4710_3 (m.d 2 3) (by simp) with h4724 | h4724
                          · linarith only [h4553, h4724, hlam]
                          · rcases p4710_3 (m.d 2 4) (by simp) with h4726 | h4726
                            · linarith only [h4726, hlam, p4710_0]
                            · rcases p4710_3 (m.d 2 5) (by simp) with h4728 | h4728
                              · linarith only [h4555, h4728, hlam]
                              · linarith only [h4658, h4728, hlam]
                        · linarith only [h4559, h4723, hlam]
                      · linarith only [h4722, hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      rcases p4710_3 (m.d 0 2) (by simp) with h4733 | h4733
                      · rcases p4710_3 (m.d 1 2) (by simp) with h4734 | h4734
                        · rcases p4710_3 (m.d 2 3) (by simp) with h4735 | h4735
                          · linarith only [h4553, h4735, hlam]
                          · rcases p4710_3 (m.d 2 4) (by simp) with h4737 | h4737
                            · linarith only [h4554, h4737, hlam]
                            · rcases p4710_3 (m.d 2 5) (by simp) with h4739 | h4739
                              · linarith only [h4739, hlam, p4710_0]
                              · rcases h5bigk with h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c | h4741c
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [hlam, p4741_0]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h2858, hlam, p4741_1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht0b, ht5b, p4741_1, u0elo4]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4553, h4556, h4562, h4658, h4709, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4741_1, u0elo1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4553, h4556, h4562, h4658, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4741_1, u0elo1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h2858, h4559, h4561, hc01, hc12, hlam, hphi, p4741_1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [hlam, p4741_0]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  rcases p4741_3 (m.d 0 5) (by simp) with h4749 | h4749
                                  · linarith only [h2858, h4749, hlam]
                                  · linarith only [h4555, h4749, hlam]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4559, h4561, h4562, h4658, h4709, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4741_1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4559, h4561, h4562, h4658, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4741_1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4555, hlam, p4741_1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4560, hlam, p4741_1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [hlam, p4741_0]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4615, hlam, p4741_1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4658, hlam, p4741_1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4556, hlam, p4741_0]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4556, hc15, hlam, hphi, ht0b, ht5b, p4741_1, u0elo4]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4553, h4556, h4562, h4658, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4741_1, u0elo1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [hlam, p4741_0]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4553, h4556, h4562, h4658, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4741_1, u0elo1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4557, hlam, p4741_0]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4561, hlam, p4741_0]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4562, h4658, h4709, hc23, hc34, hlam, hphi, p4741_1]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [h4709, hlam, p4741_0]
                                · have p4741_0 := h4741c.1
                                  have p4741_1 := h4741c.2.1
                                  have p4741_2 := h4741c.2.2.1
                                  have p4741_3 := h4741c.2.2.2
                                  linarith only [hlam, p4741_0]
                        · linarith only [h4560, h4734, hlam]
                      · linarith only [h4733, hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4553, h4556, h4615, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4710_1]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      rcases p4710_3 (m.d 0 2) (by simp) with h4773 | h4773
                      · linarith only [h0, h4773, hlam]
                      · linarith only [h4553, h4773, hlam]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      rcases p4710_3 (m.d 0 2) (by simp) with h4776 | h4776
                      · linarith only [h0, h4776, hlam]
                      · linarith only [h4554, h4776, hlam]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      rcases p4710_3 (m.d 0 2) (by simp) with h4779 | h4779
                      · linarith only [h0, h4779, hlam]
                      · linarith only [h4555, h4779, hlam]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4553, hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4558, hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4562, hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4615, hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4554, hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4559, hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4553, h4556, h4658, h4709, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4710_1, u0elo1]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4658, hlam, p4710_1]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4555, hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4560, hlam, p4710_0]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4710_1, u0elo1]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [h4553, h4556, h4658, h4709, hc24, hlam, hphi, ht0b, ht45, ht5b, p4710_1, u0elo1]
                    · have p4710_0 := h4710c.1
                      have p4710_1 := h4710c.2.1
                      have p4710_2 := h4710c.2.2.1
                      have p4710_3 := h4710c.2.2.2
                      linarith only [hlam, p4710_0]
                  · linarith only [h4554, h4557, h4562, h4709, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h2858, h4557, h4561, hlam]
        · linarith only [h0, h4555, h4560, hlam]
      · linarith only [h0, h4554, h4559, hlam]
    · linarith only [h0, h4553, h4558, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4802 | h4802
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4803 | h4803
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4804 | h4804
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4805 | h4805
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4806 | h4806
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4807 | h4807
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4808 | h4808
                · linarith only [h4554, h4557, h4808, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4810 | h4810
                  · linarith only [h4554, h4557, h4806, h4810, hlam]
                  · rcases h2bigk with h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h0, hlam, p4812_1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4807, hc35, hlam, hphi, ht0b, ht5b, p4812_1, u0elo1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      rcases p4812_3 (m.d 0 2) (by simp) with h4816 | h4816
                      · rcases p4812_3 (m.d 1 2) (by simp) with h4817 | h4817
                        · rcases p4812_3 (m.d 2 3) (by simp) with h4818 | h4818
                          · linarith only [h4553, h4818, hlam]
                          · linarith only [h4806, h4818, hlam]
                        · linarith only [h4803, h4817, hlam]
                      · linarith only [h4816, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      rcases p4812_3 (m.d 0 2) (by simp) with h4823 | h4823
                      · rcases p4812_3 (m.d 1 2) (by simp) with h4824 | h4824
                        · rcases p4812_3 (m.d 2 3) (by simp) with h4825 | h4825
                          · linarith only [h4553, h4825, hlam]
                          · linarith only [h4807, h4825, hlam]
                        · linarith only [h4804, h4824, hlam]
                      · linarith only [h4823, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4553, h4807, h4810, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4812_1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      rcases p4812_3 (m.d 0 2) (by simp) with h4832 | h4832
                      · linarith only [h0, h4832, hlam]
                      · linarith only [h4553, h4832, hlam]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      rcases p4812_3 (m.d 0 2) (by simp) with h4835 | h4835
                      · linarith only [h0, h4835, hlam]
                      · linarith only [h4554, h4835, hlam]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      rcases p4812_3 (m.d 0 2) (by simp) with h4838 | h4838
                      · linarith only [h0, h4838, hlam]
                      · linarith only [h4555, h4838, hlam]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4553, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4802, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4553, hc24, hlam, hphi, ht0b, ht45, ht5b, p4812_1, u0elo1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4553, hc25, hlam, hphi, ht0b, ht5b, p4812_1, u0elo1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4554, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4803, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4806, hlam, p4812_1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4808, hlam, p4812_1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4555, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4804, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4807, hlam, p4812_1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4555, h4806, hc34, hlam, hphi, ht0b, ht45, ht5b, p4812_1, u0elo1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [hlam, p4812_0]
              · linarith only [h4553, h4556, h4806, h4807, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4857 | h4857
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4858 | h4858
                · linarith only [h4554, h4557, h4858, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h4806, h4857, h4858, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4861 | h4861
                · linarith only [h4554, h4557, h4861, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4863 | h4863
                  · linarith only [h4556, h4557, h4863, hlam]
                  · rcases h2bigk with h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h0, hlam, p4865_1]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      rcases p4865_3 (m.d 0 2) (by simp) with h4868 | h4868
                      · rcases p4865_3 (m.d 1 2) (by simp) with h4869 | h4869
                        · rcases p4865_3 (m.d 2 3) (by simp) with h4870 | h4870
                          · linarith only [h4870, hlam, p4865_0]
                          · rcases p4865_3 (m.d 2 4) (by simp) with h4872 | h4872
                            · linarith only [h4554, h4872, hlam]
                            · linarith only [h4806, h4872, hlam]
                        · linarith only [h4802, h4869, hlam]
                      · linarith only [h4868, hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      rcases p4865_3 (m.d 0 2) (by simp) with h4877 | h4877
                      · rcases p4865_3 (m.d 1 2) (by simp) with h4878 | h4878
                        · rcases p4865_3 (m.d 2 3) (by simp) with h4879 | h4879
                          · linarith only [h4553, h4879, hlam]
                          · rcases p4865_3 (m.d 2 4) (by simp) with h4881 | h4881
                            · linarith only [h4881, hlam, p4865_0]
                            · rcases p4865_3 (m.d 2 5) (by simp) with h4883 | h4883
                              · linarith only [h4555, h4883, hlam]
                              · linarith only [h4861, h4883, hlam]
                        · linarith only [h4803, h4878, hlam]
                      · linarith only [h4877, hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      rcases p4865_3 (m.d 0 2) (by simp) with h4888 | h4888
                      · rcases p4865_3 (m.d 1 2) (by simp) with h4889 | h4889
                        · rcases p4865_3 (m.d 2 3) (by simp) with h4890 | h4890
                          · linarith only [h4553, h4890, hlam]
                          · rcases p4865_3 (m.d 2 4) (by simp) with h4892 | h4892
                            · linarith only [h4554, h4892, hlam]
                            · rcases p4865_3 (m.d 2 5) (by simp) with h4894 | h4894
                              · linarith only [h4894, hlam, p4865_0]
                              · rcases h5bigk with h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [hlam, p4896_0]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h2858, hlam, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4861, hc24, hlam, hphi, ht0b, ht45, ht5b, p4896_1, u0elo4]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4553, h4556, hc35, hlam, hphi, ht0b, ht5b, p4896_1, u0elo1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4557, hlam, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h2858, h4803, h4805, hc01, hc12, hlam, hphi, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [hlam, p4896_0]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  rcases p4896_3 (m.d 0 5) (by simp) with h4904 | h4904
                                  · linarith only [h2858, h4904, hlam]
                                  · linarith only [h4555, h4904, hlam]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4803, h4805, h4806, h4863, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4803, h4805, h4806, h4863, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4555, hlam, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4804, hlam, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [hlam, p4896_0]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4857, hlam, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4861, hlam, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4556, hlam, p4896_0]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4556, hc15, hlam, hphi, ht0b, ht5b, p4896_1, u0elo4]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4553, h4556, h4806, h4861, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4896_1, u0elo1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [hlam, p4896_0]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4863, hlam, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4803, h4805, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4805, hlam, p4896_0]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4803, h4805, h4806, h4861, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [h4803, h4805, h4857, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4896_1]
                                · have p4896_0 := h4896c.1
                                  have p4896_1 := h4896c.2.1
                                  have p4896_2 := h4896c.2.2.1
                                  have p4896_3 := h4896c.2.2.2
                                  linarith only [hlam, p4896_0]
                        · linarith only [h4804, h4889, hlam]
                      · linarith only [h4888, hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4553, h4556, h4857, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4865_1]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4803, h4805, h4806, h4863, hlam, p4865_2]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      rcases p4865_3 (m.d 0 2) (by simp) with h4929 | h4929
                      · linarith only [h0, h4929, hlam]
                      · linarith only [h4554, h4929, hlam]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      rcases p4865_3 (m.d 0 2) (by simp) with h4932 | h4932
                      · linarith only [h0, h4932, hlam]
                      · linarith only [h4555, h4932, hlam]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4553, hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4802, hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4806, hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4857, hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4554, hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4803, hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4554, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4865_1, u0elo1]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4861, hlam, p4865_1]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4555, hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4804, hlam, p4865_0]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4865_1, u0elo1]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [h4553, h4556, h4857, hc24, hlam, hphi, ht0b, ht45, ht5b, p4865_1, u0elo1]
                    · have p4865_0 := h4865c.1
                      have p4865_1 := h4865c.2.1
                      have p4865_2 := h4865c.2.2.1
                      have p4865_3 := h4865c.2.2.2
                      linarith only [hlam, p4865_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4950 | h4950
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4951 | h4951
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4952 | h4952
                · linarith only [h2858, h4554, h4805, h4952, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4954 | h4954
                  · linarith only [h4553, h4557, h4950, h4954, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases h2bigk with h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c | h4956c
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h0, hlam, p4956_1]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4951, hc35, hlam, hphi, ht0b, ht5b, p4956_1, u0elo1]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      rcases p4956_3 (m.d 0 2) (by simp) with h4960 | h4960
                      · rcases p4956_3 (m.d 1 2) (by simp) with h4961 | h4961
                        · rcases p4956_3 (m.d 2 3) (by simp) with h4962 | h4962
                          · linarith only [h4553, h4962, hlam]
                          · linarith only [h4950, h4962, hlam]
                        · linarith only [h4803, h4961, hlam]
                      · linarith only [h4960, hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      rcases p4956_3 (m.d 0 2) (by simp) with h4967 | h4967
                      · rcases p4956_3 (m.d 1 2) (by simp) with h4968 | h4968
                        · rcases p4956_3 (m.d 2 3) (by simp) with h4969 | h4969
                          · linarith only [h4553, h4969, hlam]
                          · linarith only [h4951, h4969, hlam]
                        · linarith only [h4804, h4968, hlam]
                      · linarith only [h4967, hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4553, h4951, h4954, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4956_1]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      rcases p4956_3 (m.d 0 2) (by simp) with h4976 | h4976
                      · linarith only [h0, h4976, hlam]
                      · linarith only [h4553, h4976, hlam]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      rcases p4956_3 (m.d 0 2) (by simp) with h4979 | h4979
                      · linarith only [h0, h4979, hlam]
                      · linarith only [h4554, h4979, hlam]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      rcases p4956_3 (m.d 0 2) (by simp) with h4982 | h4982
                      · linarith only [h0, h4982, hlam]
                      · linarith only [h4555, h4982, hlam]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4553, hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4802, hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4553, h4950, hc34, hlam, hphi, ht0b, ht45, ht5b, p4956_1, u0elo1]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4553, h4950, h4952, hc34, hlam, hphi, ht0b, ht45, ht5b, p4956_1, u0elo1]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4554, hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4803, hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4950, hlam, p4956_1]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4952, hlam, p4956_1]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4555, hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4804, hlam, p4956_0]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4951, hlam, p4956_1]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [h4555, h4950, hc34, hlam, hphi, ht0b, ht45, ht5b, p4956_1, u0elo1]
                    · have p4956_0 := h4956c.1
                      have p4956_1 := h4956c.2.1
                      have p4956_2 := h4956c.2.2.1
                      have p4956_3 := h4956c.2.2.2
                      linarith only [hlam, p4956_0]
              · linarith only [h4553, h4556, h4950, h4951, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5001 | h5001
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5002 | h5002
                · linarith only [h4554, h4557, h5002, hlam]
                · linarith only [h4950, h5001, h5002, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5005 | h5005
                · linarith only [h4554, h4557, h5005, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5007 | h5007
                  · linarith only [h4556, h4557, h5007, hlam]
                  · rcases h2bigk with h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h0, hlam, p5009_1]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      rcases p5009_3 (m.d 0 2) (by simp) with h5012 | h5012
                      · rcases p5009_3 (m.d 1 2) (by simp) with h5013 | h5013
                        · rcases p5009_3 (m.d 2 3) (by simp) with h5014 | h5014
                          · linarith only [h5014, hlam, p5009_0]
                          · rcases p5009_3 (m.d 2 4) (by simp) with h5016 | h5016
                            · linarith only [h4554, h5016, hlam]
                            · linarith only [h4950, h5016, hlam]
                        · linarith only [h4802, h5013, hlam]
                      · linarith only [h5012, hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      rcases p5009_3 (m.d 0 2) (by simp) with h5021 | h5021
                      · rcases p5009_3 (m.d 1 2) (by simp) with h5022 | h5022
                        · rcases p5009_3 (m.d 2 3) (by simp) with h5023 | h5023
                          · linarith only [h4553, h5023, hlam]
                          · rcases p5009_3 (m.d 2 4) (by simp) with h5025 | h5025
                            · linarith only [h5025, hlam, p5009_0]
                            · rcases p5009_3 (m.d 2 5) (by simp) with h5027 | h5027
                              · linarith only [h4555, h5027, hlam]
                              · linarith only [h5005, h5027, hlam]
                        · linarith only [h4803, h5022, hlam]
                      · linarith only [h5021, hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      rcases p5009_3 (m.d 0 2) (by simp) with h5032 | h5032
                      · rcases p5009_3 (m.d 1 2) (by simp) with h5033 | h5033
                        · rcases p5009_3 (m.d 2 3) (by simp) with h5034 | h5034
                          · linarith only [h4553, h5034, hlam]
                          · rcases p5009_3 (m.d 2 4) (by simp) with h5036 | h5036
                            · linarith only [h4554, h5036, hlam]
                            · rcases p5009_3 (m.d 2 5) (by simp) with h5038 | h5038
                              · linarith only [h5038, hlam, p5009_0]
                              · rcases h5bigk with h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [hlam, p5040_0]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h2858, hlam, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h5005, hc24, hlam, hphi, ht0b, ht45, ht5b, p5040_1, u0elo4]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h4553, h4556, hc35, hlam, hphi, ht0b, ht5b, p5040_1, u0elo1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h4557, hlam, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h2858, hc01, hc15, hlam, hphi, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [hlam, p5040_0]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h4805, h5005, hc24, hc45, hlam, hphi, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h4805, h4950, h5007, hc23, hc45, hlam, hphi, ht34, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h4805, hlam, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h4555, hlam, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h4804, hlam, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [hlam, p5040_0]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h5001, hlam, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h5005, hlam, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h4556, hlam, p5040_0]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h4556, hc15, hlam, hphi, ht0b, ht5b, p5040_1, u0elo4]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h4553, h4556, h4950, h5005, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5040_1, u0elo1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [hlam, p5040_0]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h5007, hlam, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h2858, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h2858, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h4950, h5005, hc23, hc45, hlam, hphi, ht34, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [h5001, hc23, hc45, hlam, hphi, ht34, p5040_1]
                                · have p5040_0 := h5040c.1
                                  have p5040_1 := h5040c.2.1
                                  have p5040_2 := h5040c.2.2.1
                                  have p5040_3 := h5040c.2.2.2
                                  linarith only [hlam, p5040_0]
                        · linarith only [h4804, h5033, hlam]
                      · linarith only [h5032, hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h4553, h4556, h5001, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5009_1]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      rcases p5009_3 (m.d 0 2) (by simp) with h5070 | h5070
                      · linarith only [h0, h5070, hlam]
                      · linarith only [h4553, h5070, hlam]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      rcases p5009_3 (m.d 0 2) (by simp) with h5073 | h5073
                      · linarith only [h0, h5073, hlam]
                      · linarith only [h4554, h5073, hlam]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      rcases p5009_3 (m.d 0 2) (by simp) with h5076 | h5076
                      · linarith only [h0, h5076, hlam]
                      · linarith only [h4555, h5076, hlam]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h4553, hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h4802, hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h4950, hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h5001, hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h4554, hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h4803, hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h4554, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5009_1, u0elo1]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h5005, hlam, p5009_1]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h4555, hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h4804, hlam, p5009_0]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h4553, h4556, h5001, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5009_1, u0elo1]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [h4553, h4556, h5001, hc24, hlam, hphi, ht0b, ht45, ht5b, p5009_1, u0elo1]
                    · have p5009_0 := h5009c.1
                      have p5009_1 := h5009c.2.1
                      have p5009_2 := h5009c.2.2.1
                      have p5009_3 := h5009c.2.2.2
                      linarith only [hlam, p5009_0]
        · linarith only [h0, h4555, h4804, hlam]
      · linarith only [h0, h4554, h4803, hlam]
    · linarith only [h0, h4553, h4802, hlam]

set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4554 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4555 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4556 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5097 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 1 2 3 (by decide) (by decide) with h5098 | h5098
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5099 | h5099
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5100 | h5100
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5101 | h5101
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5102 | h5102
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5103 | h5103
            · linarith only [h4553, h4556, h5103, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5105 | h5105
              · linarith only [h5102, h5103, h5105, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5107 | h5107
                · linarith only [h5102, h5103, h5105, h5107, hlam]
                · linarith only [h4553, h4554, h4556, h5097, h5102, h5107, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5110 | h5110
            · linarith only [h4553, h4556, h5110, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5112 | h5112
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5113 | h5113
                · rcases h2bigk with h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h0, hlam, p5114_1]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    rcases p5114_3 (m.d 0 2) (by simp) with h5117 | h5117
                    · rcases p5114_3 (m.d 1 2) (by simp) with h5118 | h5118
                      · rcases p5114_3 (m.d 2 3) (by simp) with h5119 | h5119
                        · linarith only [h5119, hlam, p5114_0]
                        · rcases p5114_3 (m.d 2 4) (by simp) with h5121 | h5121
                          · linarith only [h4554, h5121, hlam]
                          · linarith only [h5102, h5121, hlam]
                      · linarith only [h5098, h5118, hlam]
                    · linarith only [h5117, hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h5112, hc45, hlam, hphi, ht0b, ht5b, p5114_1, u0elo1]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    rcases p5114_3 (m.d 0 2) (by simp) with h5127 | h5127
                    · rcases p5114_3 (m.d 1 2) (by simp) with h5128 | h5128
                      · rcases p5114_3 (m.d 2 3) (by simp) with h5129 | h5129
                        · linarith only [h4553, h5129, hlam]
                        · rcases p5114_3 (m.d 2 4) (by simp) with h5131 | h5131
                          · linarith only [h4554, h5131, hlam]
                          · linarith only [h5112, h5131, hlam]
                      · linarith only [h5100, h5128, hlam]
                    · linarith only [h5127, hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h4554, h5112, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5114_1]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    rcases p5114_3 (m.d 0 2) (by simp) with h5138 | h5138
                    · linarith only [h0, h5138, hlam]
                    · linarith only [h4553, h5138, hlam]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    rcases p5114_3 (m.d 0 2) (by simp) with h5141 | h5141
                    · linarith only [h0, h5141, hlam]
                    · linarith only [h4554, h5141, hlam]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    rcases p5114_3 (m.d 0 2) (by simp) with h5144 | h5144
                    · linarith only [h0, h5144, hlam]
                    · linarith only [h4555, h5144, hlam]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h4553, hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h5098, hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h5102, hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h5110, hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h4554, hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h5099, hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h4554, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5114_1, u0elo1]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h4554, h5110, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5114_1, u0elo1]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h4555, hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h5100, hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h4555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5114_1, u0elo1]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [h5112, hlam, p5114_0]
                  · have p5114_0 := h5114c.1
                    have p5114_1 := h5114c.2.1
                    have p5114_2 := h5114c.2.2.1
                    have p5114_3 := h5114c.2.2.2
                    linarith only [hlam, p5114_0]
                · linarith only [h4554, h5097, h5102, h5113, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5163 | h5163
                · rcases h2bigk with h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h0, hlam, p5164_1]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    rcases p5164_3 (m.d 0 2) (by simp) with h5167 | h5167
                    · rcases p5164_3 (m.d 1 2) (by simp) with h5168 | h5168
                      · rcases p5164_3 (m.d 2 3) (by simp) with h5169 | h5169
                        · linarith only [h5169, hlam, p5164_0]
                        · rcases p5164_3 (m.d 2 4) (by simp) with h5171 | h5171
                          · linarith only [h4554, h5171, hlam]
                          · linarith only [h5102, h5171, hlam]
                      · linarith only [h5098, h5168, hlam]
                    · linarith only [h5167, hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    rcases p5164_3 (m.d 0 2) (by simp) with h5176 | h5176
                    · rcases p5164_3 (m.d 1 2) (by simp) with h5177 | h5177
                      · rcases p5164_3 (m.d 2 3) (by simp) with h5178 | h5178
                        · linarith only [h4553, h5178, hlam]
                        · rcases p5164_3 (m.d 2 4) (by simp) with h5180 | h5180
                          · linarith only [h5180, hlam, p5164_0]
                          · rcases p5164_3 (m.d 2 5) (by simp) with h5182 | h5182
                            · linarith only [h4555, h5182, hlam]
                            · linarith only [h5112, h5182, hlam]
                      · linarith only [h5099, h5177, hlam]
                    · linarith only [h5176, hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    rcases p5164_3 (m.d 0 2) (by simp) with h5187 | h5187
                    · rcases p5164_3 (m.d 1 2) (by simp) with h5188 | h5188
                      · rcases p5164_3 (m.d 2 3) (by simp) with h5189 | h5189
                        · linarith only [h4553, h5189, hlam]
                        · rcases p5164_3 (m.d 2 4) (by simp) with h5191 | h5191
                          · linarith only [h4554, h5191, hlam]
                          · rcases p5164_3 (m.d 2 5) (by simp) with h5193 | h5193
                            · linarith only [h5193, hlam, p5164_0]
                            · rcases h5bigk with h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [hlam, p5195_0]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h2858, hlam, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5112, hc24, hlam, hphi, ht0b, ht45, ht5b, p5195_1, u0elo4]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h4556, hlam, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h4554, h5097, hc45, hlam, hphi, ht0b, ht5b, p5195_1, u0elo1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h2858, h5099, h5101, hc01, hc12, hlam, hphi, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [hlam, p5195_0]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                rcases p5195_3 (m.d 0 5) (by simp) with h5203 | h5203
                                · linarith only [h2858, h5203, hlam]
                                · linarith only [h4555, h5203, hlam]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h4556, h5097, h5099, h5101, h5102, h5112, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5099, h5101, h5102, h5112, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h4555, hlam, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5100, hlam, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [hlam, p5195_0]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5110, hlam, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5112, hlam, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5097, h5102, h5112, hc23, hc35, hlam, hphi, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h2858, h5163, hc01, hc34, hlam, hphi, ht12, ht23, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5102, h5112, h5163, hc23, hc34, hlam, hphi, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [hlam, p5195_0]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5102, h5112, h5163, hc23, hc34, hlam, hphi, p5195_1]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5097, hlam, p5195_0]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5101, hlam, p5195_0]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5097, h5102, h5112, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5195_1, u0elo4]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [h5163, hlam, p5195_0]
                              · have p5195_0 := h5195c.1
                                have p5195_1 := h5195c.2.1
                                have p5195_2 := h5195c.2.2.1
                                have p5195_3 := h5195c.2.2.2
                                linarith only [hlam, p5195_0]
                      · linarith only [h5100, h5188, hlam]
                    · linarith only [h5187, hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h4554, h5097, h5102, h5112, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5164_1]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    rcases p5164_3 (m.d 0 2) (by simp) with h5227 | h5227
                    · linarith only [h0, h5227, hlam]
                    · linarith only [h4553, h5227, hlam]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    rcases p5164_3 (m.d 0 2) (by simp) with h5230 | h5230
                    · linarith only [h0, h5230, hlam]
                    · linarith only [h4554, h5230, hlam]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    rcases p5164_3 (m.d 0 2) (by simp) with h5233 | h5233
                    · linarith only [h0, h5233, hlam]
                    · linarith only [h4555, h5233, hlam]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h4553, hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h5098, hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h5102, hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h5110, hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h4554, hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h5099, hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h4554, h5097, h5112, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5164_1, u0elo1]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h5112, hlam, p5164_1]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h4555, hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h5100, hlam, p5164_0]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h4555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5164_1, u0elo1]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [h4554, h5097, h5112, hc24, hlam, hphi, ht0b, ht45, ht5b, p5164_1, u0elo1]
                  · have p5164_0 := h5164c.1
                    have p5164_1 := h5164c.2.1
                    have p5164_2 := h5164c.2.2.1
                    have p5164_3 := h5164c.2.2.2
                    linarith only [hlam, p5164_0]
                · linarith only [h4554, h5097, h5102, h5163, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
        · linarith only [h2858, h5097, h5101, hlam]
      · linarith only [h0, h4555, h5100, hlam]
    · linarith only [h0, h4554, h5099, hlam]
  · linarith only [h0, h4553, h5098, hlam]

end R2N4
