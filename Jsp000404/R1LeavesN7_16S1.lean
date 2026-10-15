import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5636000 in
theorem r1l7_21_15_H_I_L_I_s6_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 4 (by decide) (by decide) with h555 | h555
  · rcases m.htr 1 2 5 (by decide) (by decide) with h556 | h556
    · rcases m.htr 1 3 4 (by decide) (by decide) with h557 | h557
      · rcases m.htr 1 3 5 (by decide) (by decide) with h558 | h558
        · rcases m.htr 1 4 5 (by decide) (by decide) with h559 | h559
          · rcases m.htr 2 3 4 (by decide) (by decide) with h560 | h560
            · rcases m.htr 2 3 5 (by decide) (by decide) with h561 | h561
              · rcases m.htr 2 4 5 (by decide) (by decide) with h562 | h562
                · linarith only [h0, h10, h4, h555, h562, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h10, h4, h555, h559, h562, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10, h4, h556, h561, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h10, h556, h560, h7, hc03, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h567 | h567
            · rcases m.htr 2 3 5 (by decide) (by decide) with h568 | h568
              · rcases m.htr 2 4 5 (by decide) (by decide) with h569 | h569
                · linarith only [h10, h555, h559, h569, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h571 | h571
                  · linarith only [h0, h10, h4, h555, h559, h567, h571, hc01, hc15, hlam, hphi, ht0b, ht5b]
                  · rcases h1bigk with h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h556, h569, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p573_1]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h10, h556, h567, h569, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p573_1]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      rcases p573_3 (m.d 0 1) (by simp) with h577 | h577
                      · rcases p573_3 (m.d 1 2) (by simp) with h578 | h578
                        · linarith only [h0, h578, hlam]
                        · linarith only [h555, h578, hlam]
                      · linarith only [h577, hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      rcases p573_3 (m.d 0 1) (by simp) with h582 | h582
                      · rcases p573_3 (m.d 1 2) (by simp) with h583 | h583
                        · linarith only [h0, h583, hlam]
                        · linarith only [h556, h583, hlam]
                      · linarith only [h582, hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h0, hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h10, hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h10, h4, h555, h567, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p573_1]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h0, h10, h4, h555, h559, h567, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p573_1]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h1, hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p573_1]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h0, h10, h4, h555, h567, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p573_1]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h0, h10, h4, h555, h559, h567, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p573_1]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h2, hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h555, hlam, p573_1]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h557, hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h559, hlam, p573_1]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h3, hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h556, hlam, p573_1]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h558, hlam, p573_0]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [h3, h555, h567, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p573_1]
                    · have p573_0 := h573c.1
                      have p573_1 := h573c.2.1
                      have p573_2 := h573c.2.2.1
                      have p573_3 := h573c.2.2.2
                      linarith only [hlam, p573_0]
              · linarith only [h0, h10, h4, h555, h567, h568, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h555, h567, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h10, h556, h558, hlam]
      · linarith only [h10, h555, h557, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h611 | h611
      · rcases m.htr 1 3 5 (by decide) (by decide) with h612 | h612
        · rcases m.htr 1 4 5 (by decide) (by decide) with h613 | h613
          · linarith only [h555, h556, h613, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h615 | h615
            · rcases m.htr 2 3 5 (by decide) (by decide) with h616 | h616
              · rcases m.htr 2 4 5 (by decide) (by decide) with h617 | h617
                · linarith only [h555, h556, h613, h616, h617, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h619 | h619
                  · linarith only [h555, h556, h615, h617, h619, hlam]
                  · rcases h1bigk with h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h555, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p621_1]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h555, h556, h612, h615, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p621_1]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      rcases p621_3 (m.d 0 1) (by simp) with h625 | h625
                      · rcases p621_3 (m.d 1 2) (by simp) with h626 | h626
                        · linarith only [h0, h626, hlam]
                        · linarith only [h555, h626, hlam]
                      · linarith only [h625, hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h555, h556, h615, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p621_1]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h0, hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h10, hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h4, h555, h556, h615, h617, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p621_1]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h556, hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h1, hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p621_1]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h0, h10, h4, h555, h615, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p621_1]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h0, h10, h4, h555, h556, h615, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p621_1]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h2, hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h555, hlam, p621_1]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h611, hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h613, hlam, p621_1]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h3, hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h555, h615, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p621_1]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h612, hlam, p621_0]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [h0, h4, h555, h556, h615, h617, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p621_1]
                    · have p621_0 := h621c.1
                      have p621_1 := h621c.2.1
                      have p621_2 := h621c.2.2.1
                      have p621_3 := h621c.2.2.2
                      linarith only [hlam, p621_0]
              · linarith only [h0, h10, h4, h555, h615, h616, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h555, h615, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h653 | h653
          · linarith only [h555, h556, h653, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h655 | h655
            · rcases m.htr 2 3 5 (by decide) (by decide) with h656 | h656
              · linarith only [h0, h10, h4, h555, h612, h655, h656, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10, h4, h555, h655, h656, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h555, h655, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h555, h611, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h661 | h661
    · rcases m.htr 1 3 4 (by decide) (by decide) with h662 | h662
      · rcases m.htr 1 3 5 (by decide) (by decide) with h663 | h663
        · rcases m.htr 1 4 5 (by decide) (by decide) with h664 | h664
          · rcases m.htr 2 3 4 (by decide) (by decide) with h665 | h665
            · rcases m.htr 2 3 5 (by decide) (by decide) with h666 | h666
              · rcases m.htr 2 4 5 (by decide) (by decide) with h667 | h667
                · rcases m.htr 3 4 5 (by decide) (by decide) with h668 | h668
                  · rcases h1bigk with h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h661, h666, h668, hc01, hc45, hlam, hphi, ht0b, ht5b, p669_1]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h662, h668, hc01, hc45, hlam, hphi, ht0b, ht5b, p669_1]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h555, h661, h666, h668, hc01, hc45, hlam, hphi, ht0b, ht5b, p669_1]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      rcases p669_3 (m.d 0 1) (by simp) with h674 | h674
                      · rcases p669_3 (m.d 1 2) (by simp) with h675 | h675
                        · linarith only [h0, h675, hlam]
                        · linarith only [h661, h675, hlam]
                      · linarith only [h674, hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h0, hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h10, hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h555, hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h555, h661, h666, h668, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p669_1]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h1, hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p669_1]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h0, h10, h4, h555, h661, h666, h668, hc01, hc45, hlam, hphi, ht0b, ht5b, p669_1]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h0, h10, h4, h661, h666, h668, hc01, hc45, hlam, hphi, ht0b, ht5b, p669_1]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h2, hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h661, h666, h668, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p669_1]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h662, hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h0, h10, h4, h661, h662, h666, h668, hc01, hc45, hlam, hphi, ht0b, ht5b, p669_1]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h3, hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h661, hlam, p669_1]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h663, hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [h664, hlam, p669_0]
                    · have p669_0 := h669c.1
                      have p669_1 := h669c.2.1
                      have p669_2 := h669c.2.2.1
                      have p669_3 := h669c.2.2.2
                      linarith only [hlam, p669_0]
                  · linarith only [h0, h4, h555, h661, h665, h667, h668, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h4, h555, h661, h667, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h4, h555, h661, h665, h666, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h4, h661, h665, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h555, h661, h664, hlam]
        · linarith only [h10, h661, h663, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h705 | h705
        · rcases m.htr 1 4 5 (by decide) (by decide) with h706 | h706
          · rcases m.htr 2 3 4 (by decide) (by decide) with h707 | h707
            · linarith only [h0, h4, h662, h705, h707, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h4, h661, h7, h707, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h10, h661, h662, h706, hlam]
        · linarith only [h10, h661, h705, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h712 | h712
      · rcases m.htr 1 3 5 (by decide) (by decide) with h713 | h713
        · rcases m.htr 1 4 5 (by decide) (by decide) with h714 | h714
          · rcases m.htr 2 3 4 (by decide) (by decide) with h715 | h715
            · rcases m.htr 2 3 5 (by decide) (by decide) with h716 | h716
              · rcases m.htr 2 4 5 (by decide) (by decide) with h717 | h717
                · rcases m.htr 3 4 5 (by decide) (by decide) with h718 | h718
                  · rcases h1bigk with h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      rcases p719_3 (m.d 0 1) (by simp) with h721 | h721
                      · rcases p719_3 (m.d 1 2) (by simp) with h722 | h722
                        · linarith only [h722, hlam, p719_0]
                        · rcases p719_3 (m.d 1 3) (by simp) with h724 | h724
                          · linarith only [h1, h724, hlam]
                          · linarith only [h10, h724, hlam]
                      · linarith only [h721, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h712, h718, hc01, hc45, hlam, hphi, ht0b, ht5b, p719_1]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h712, h718, hc01, hc45, hlam, hphi, ht0b, ht5b, p719_1]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      rcases p719_3 (m.d 0 1) (by simp) with h730 | h730
                      · rcases p719_3 (m.d 1 2) (by simp) with h731 | h731
                        · linarith only [h0, h731, hlam]
                        · rcases p719_3 (m.d 1 3) (by simp) with h733 | h733
                          · linarith only [h1, h733, hlam]
                          · linarith only [h713, h733, hlam]
                      · linarith only [h730, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h0, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h10, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h555, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h661, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h1, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p719_1]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h0, h10, h4, h712, h718, hc01, hc45, hlam, hphi, ht0b, ht5b, p719_1]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h0, h10, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p719_1]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h2, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p719_1]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h712, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h0, h4, h555, h661, h715, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p719_1]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h3, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p719_1]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h713, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [h714, hlam, p719_0]
                    · have p719_0 := h719c.1
                      have p719_1 := h719c.2.1
                      have p719_2 := h719c.2.2.1
                      have p719_3 := h719c.2.2.2
                      linarith only [hlam, p719_0]
                  · rcases h1bigk with h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      rcases p757_3 (m.d 0 1) (by simp) with h759 | h759
                      · rcases p757_3 (m.d 1 2) (by simp) with h760 | h760
                        · linarith only [h760, hlam, p757_0]
                        · rcases p757_3 (m.d 1 3) (by simp) with h762 | h762
                          · linarith only [h1, h762, hlam]
                          · linarith only [h10, h762, hlam]
                      · linarith only [h759, hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h712, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p757_1]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h714, hc01, hc45, hlam, hphi, ht0b, ht5b, p757_1]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h714, h718, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p757_1]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h0, hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h10, hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h555, hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h661, hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h1, hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p757_1]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h0, h10, h4, h714, h718, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p757_1]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h0, h10, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p757_1]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h2, hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p757_1]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h712, hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h0, h4, h555, h661, h715, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p757_1]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h3, hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p757_1]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h713, hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [h714, hlam, p757_0]
                    · have p757_0 := h757c.1
                      have p757_1 := h757c.2.1
                      have p757_2 := h757c.2.2.1
                      have p757_3 := h757c.2.2.2
                      linarith only [hlam, p757_0]
                · linarith only [h555, h714, h717, hlam]
              · linarith only [h10, h713, h716, hlam]
            · linarith only [h10, h712, h715, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h792 | h792
            · rcases m.htr 2 3 5 (by decide) (by decide) with h793 | h793
              · rcases m.htr 2 4 5 (by decide) (by decide) with h794 | h794
                · rcases m.htr 3 4 5 (by decide) (by decide) with h795 | h795
                  · linarith only [h1, h712, h714, h795, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h1bigk with h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      rcases p797_3 (m.d 0 1) (by simp) with h799 | h799
                      · rcases p797_3 (m.d 1 2) (by simp) with h800 | h800
                        · linarith only [h800, hlam, p797_0]
                        · rcases p797_3 (m.d 1 3) (by simp) with h802 | h802
                          · linarith only [h1, h802, hlam]
                          · linarith only [h10, h802, hlam]
                      · linarith only [h799, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h712, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p797_1]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      rcases p797_3 (m.d 0 1) (by simp) with h807 | h807
                      · rcases p797_3 (m.d 1 2) (by simp) with h808 | h808
                        · linarith only [h0, h808, hlam]
                        · rcases p797_3 (m.d 1 3) (by simp) with h810 | h810
                          · linarith only [h1, h810, hlam]
                          · linarith only [h712, h810, hlam]
                      · linarith only [h807, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      rcases p797_3 (m.d 0 1) (by simp) with h814 | h814
                      · rcases p797_3 (m.d 1 2) (by simp) with h815 | h815
                        · linarith only [h0, h815, hlam]
                        · rcases p797_3 (m.d 1 3) (by simp) with h817 | h817
                          · linarith only [h1, h817, hlam]
                          · linarith only [h713, h817, hlam]
                      · linarith only [h814, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h0, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h10, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h555, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h661, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h1, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p797_1]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h0, h10, h4, h555, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p797_1]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h0, h10, h4, h555, h714, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p797_1]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h2, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h714, hc12, hc45, hlam, hphi, ht23, ht34, p797_1]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h712, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h714, hlam, p797_1]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h3, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p797_1]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h713, hlam, p797_0]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [h0, h4, h661, h792, h794, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p797_1]
                    · have p797_0 := h797c.1
                      have p797_1 := h797c.2.1
                      have p797_2 := h797c.2.2.1
                      have p797_3 := h797c.2.2.2
                      linarith only [hlam, p797_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h841 | h841
                  · linarith only [h0, h4, h555, h7, h794, h841, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h1bigk with h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      rcases p843_3 (m.d 0 1) (by simp) with h845 | h845
                      · rcases p843_3 (m.d 1 2) (by simp) with h846 | h846
                        · linarith only [h846, hlam, p843_0]
                        · rcases p843_3 (m.d 1 3) (by simp) with h848 | h848
                          · linarith only [h1, h848, hlam]
                          · linarith only [h10, h848, hlam]
                      · linarith only [h845, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h712, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p843_1]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      rcases p843_3 (m.d 0 1) (by simp) with h853 | h853
                      · rcases p843_3 (m.d 1 2) (by simp) with h854 | h854
                        · linarith only [h0, h854, hlam]
                        · rcases p843_3 (m.d 1 3) (by simp) with h856 | h856
                          · linarith only [h1, h856, hlam]
                          · linarith only [h712, h856, hlam]
                      · linarith only [h853, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      rcases p843_3 (m.d 0 1) (by simp) with h860 | h860
                      · rcases p843_3 (m.d 1 2) (by simp) with h861 | h861
                        · linarith only [h0, h861, hlam]
                        · rcases p843_3 (m.d 1 3) (by simp) with h863 | h863
                          · linarith only [h1, h863, hlam]
                          · linarith only [h713, h863, hlam]
                      · linarith only [h860, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h0, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h10, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h555, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h661, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h1, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p843_1]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h0, h10, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p843_1]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h0, h10, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p843_1]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h2, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p843_1]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h712, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h714, hlam, p843_1]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h3, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p843_1]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h713, hlam, p843_0]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [h661, h794, hc14, hc45, hlam, hphi, p843_1]
                    · have p843_0 := h843c.1
                      have p843_1 := h843c.2.1
                      have p843_2 := h843c.2.2.1
                      have p843_3 := h843c.2.2.2
                      linarith only [hlam, p843_0]
              · linarith only [h10, h713, h793, hlam]
            · linarith only [h10, h712, h792, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h889 | h889
          · linarith only [h712, h713, h889, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h891 | h891
            · rcases m.htr 2 3 5 (by decide) (by decide) with h892 | h892
              · linarith only [h0, h4, h712, h713, h892, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h894 | h894
                · linarith only [h0, h4, h8, h889, h891, h892, h894, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h896 | h896
                  · linarith only [h0, h10, h4, h712, h8, h892, h894, h896, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · rcases h1bigk with h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      rcases p898_3 (m.d 0 1) (by simp) with h900 | h900
                      · rcases p898_3 (m.d 1 2) (by simp) with h901 | h901
                        · linarith only [h901, hlam, p898_0]
                        · rcases p898_3 (m.d 1 3) (by simp) with h903 | h903
                          · linarith only [h1, h903, hlam]
                          · linarith only [h10, h903, hlam]
                      · linarith only [h900, hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h712, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p898_1]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      rcases p898_3 (m.d 0 1) (by simp) with h908 | h908
                      · rcases p898_3 (m.d 1 2) (by simp) with h909 | h909
                        · linarith only [h0, h909, hlam]
                        · rcases p898_3 (m.d 1 3) (by simp) with h911 | h911
                          · linarith only [h1, h911, hlam]
                          · linarith only [h712, h911, hlam]
                      · linarith only [h908, hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h712, h713, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p898_1]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h0, hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h10, hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h555, hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h661, hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h1, hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p898_1]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h10, h555, hc12, hc23, hlam, hphi, p898_1]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h713, hlam, p898_1]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h2, hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p898_1]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h712, hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h889, hlam, p898_1]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h3, hlam, p898_0]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p898_1]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h0, h4, h713, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p898_1]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [h0, h4, h555, h7, h889, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p898_1]
                    · have p898_0 := h898c.1
                      have p898_1 := h898c.2.1
                      have p898_2 := h898c.2.2.1
                      have p898_3 := h898c.2.2.2
                      linarith only [hlam, p898_0]
            · linarith only [h1, h10, h712, h891, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h937 | h937
        · rcases m.htr 1 4 5 (by decide) (by decide) with h938 | h938
          · rcases m.htr 2 3 4 (by decide) (by decide) with h939 | h939
            · linarith only [h0, h4, h712, h937, h939, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h941 | h941
              · rcases m.htr 2 4 5 (by decide) (by decide) with h942 | h942
                · rcases m.htr 3 4 5 (by decide) (by decide) with h943 | h943
                  · rcases h1bigk with h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      rcases p944_3 (m.d 0 1) (by simp) with h946 | h946
                      · rcases p944_3 (m.d 1 2) (by simp) with h947 | h947
                        · linarith only [h947, hlam, p944_0]
                        · rcases p944_3 (m.d 1 3) (by simp) with h949 | h949
                          · linarith only [h1, h949, hlam]
                          · linarith only [h10, h949, hlam]
                      · linarith only [h946, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h937, h943, hc01, hc45, hlam, hphi, ht0b, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h712, h937, h943, hc01, hc45, hlam, hphi, ht0b, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      rcases p944_3 (m.d 0 1) (by simp) with h955 | h955
                      · rcases p944_3 (m.d 1 2) (by simp) with h956 | h956
                        · linarith only [h0, h956, hlam]
                        · rcases p944_3 (m.d 1 3) (by simp) with h958 | h958
                          · linarith only [h1, h958, hlam]
                          · linarith only [h937, h958, hlam]
                      · linarith only [h955, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h10, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h555, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h661, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h1, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h712, hlam, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, h4, h7, h712, hc01, hc15, hlam, hphi, ht0b, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h2, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, h4, h555, h7, h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, h4, h555, h7, h939, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, h4, h555, h661, h7, h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h3, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h937, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h938, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [hlam, p944_0]
                  · linarith only [h0, h10, h4, h7, h9, h939, h943, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h10, h555, h937, h938, h939, h942, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h10, h937, h941, hlam]
          · linarith only [h712, h937, h938, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h986 | h986
          · rcases m.htr 2 3 4 (by decide) (by decide) with h987 | h987
            · rcases m.htr 2 3 5 (by decide) (by decide) with h988 | h988
              · rcases m.htr 2 4 5 (by decide) (by decide) with h989 | h989
                · rcases m.htr 3 4 5 (by decide) (by decide) with h990 | h990
                  · rcases h1bigk with h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      rcases p991_3 (m.d 0 1) (by simp) with h993 | h993
                      · rcases p991_3 (m.d 1 2) (by simp) with h994 | h994
                        · linarith only [h994, hlam, p991_0]
                        · rcases p991_3 (m.d 1 3) (by simp) with h996 | h996
                          · linarith only [h1, h996, hlam]
                          · linarith only [h10, h996, hlam]
                      · linarith only [h993, hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      rcases p991_3 (m.d 0 1) (by simp) with h1000 | h1000
                      · rcases p991_3 (m.d 1 2) (by simp) with h1001 | h1001
                        · linarith only [h0, h1001, hlam]
                        · rcases p991_3 (m.d 1 3) (by simp) with h1003 | h1003
                          · linarith only [h1003, hlam, p991_0]
                          · rcases p991_3 (m.d 1 4) (by simp) with h1005 | h1005
                            · linarith only [h1005, h2, hlam]
                            · linarith only [h1005, h712, hlam]
                      · linarith only [h1000, hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h986, hc01, hc45, hlam, hphi, ht0b, ht5b, p991_1]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      rcases p991_3 (m.d 0 1) (by simp) with h1010 | h1010
                      · rcases p991_3 (m.d 1 2) (by simp) with h1011 | h1011
                        · linarith only [h0, h1011, hlam]
                        · rcases p991_3 (m.d 1 3) (by simp) with h1013 | h1013
                          · linarith only [h1, h1013, hlam]
                          · rcases p991_3 (m.d 1 4) (by simp) with h1015 | h1015
                            · linarith only [h1015, h2, hlam]
                            · linarith only [h1015, h986, hlam]
                      · linarith only [h1010, hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h0, hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h10, hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h555, hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h661, hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h1, hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h937, hc12, hc35, hlam, hphi, ht23, p991_1]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h712, hlam, p991_1]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h937, hlam, p991_1]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h2, hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p991_1]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h0, h4, h712, h987, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p991_1]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h0, h4, h712, h987, hc01, hc15, hlam, hphi, ht0b, ht5b, p991_1]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h3, hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p991_1]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h10, h661, h989, hc12, hc24, hlam, hphi, p991_1]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [h986, hlam, p991_0]
                    · have p991_0 := h991c.1
                      have p991_1 := h991c.2.1
                      have p991_2 := h991c.2.2.1
                      have p991_3 := h991c.2.2.2
                      linarith only [hlam, p991_0]
                  · linarith only [h712, h986, h990, hlam]
                · linarith only [h2, h555, h986, h989, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h10, h712, h987, h988, hc12, hc35, hlam, hphi, ht23]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1042 | h1042
              · linarith only [h0, h10, h1042, h4, h7, h937, h987, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1044 | h1044
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1045 | h1045
                  · rcases h1bigk with h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      rcases p1046_3 (m.d 0 1) (by simp) with h1048 | h1048
                      · rcases p1046_3 (m.d 1 2) (by simp) with h1049 | h1049
                        · linarith only [h1049, hlam, p1046_0]
                        · rcases p1046_3 (m.d 1 3) (by simp) with h1051 | h1051
                          · linarith only [h1, h1051, hlam]
                          · linarith only [h10, h1051, hlam]
                      · linarith only [h1048, hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      rcases p1046_3 (m.d 0 1) (by simp) with h1055 | h1055
                      · rcases p1046_3 (m.d 1 2) (by simp) with h1056 | h1056
                        · linarith only [h0, h1056, hlam]
                        · rcases p1046_3 (m.d 1 3) (by simp) with h1058 | h1058
                          · linarith only [h1058, hlam, p1046_0]
                          · rcases p1046_3 (m.d 1 4) (by simp) with h1060 | h1060
                            · linarith only [h1060, h2, hlam]
                            · linarith only [h1060, h712, hlam]
                      · linarith only [h1055, hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h986, hc01, hc45, hlam, hphi, ht0b, ht5b, p1046_1]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      rcases p1046_3 (m.d 0 1) (by simp) with h1065 | h1065
                      · rcases p1046_3 (m.d 1 2) (by simp) with h1066 | h1066
                        · linarith only [h0, h1066, hlam]
                        · rcases p1046_3 (m.d 1 3) (by simp) with h1068 | h1068
                          · linarith only [h1, h1068, hlam]
                          · rcases p1046_3 (m.d 1 4) (by simp) with h1070 | h1070
                            · linarith only [h1070, h2, hlam]
                            · linarith only [h1070, h986, hlam]
                      · linarith only [h1065, hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h0, hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h10, hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h555, hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h661, hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h1, hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1046_1]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h712, hlam, p1046_1]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h937, hlam, p1046_1]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h2, hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1046_1]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h0, h4, h555, h7, h987, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1046_1]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h0, h4, h555, h7, h987, hc01, hc15, hlam, hphi, ht0b, ht5b, p1046_1]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h3, hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1046_1]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h0, h10, h1044, h4, h661, h7, h987, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1046_1]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [h986, hlam, p1046_0]
                    · have p1046_0 := h1046c.1
                      have p1046_1 := h1046c.2.1
                      have p1046_2 := h1046c.2.2.1
                      have p1046_3 := h1046c.2.2.2
                      linarith only [hlam, p1046_0]
                  · linarith only [h1045, h555, h986, h987, hlam]
                · linarith only [h1044, h555, h986, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1096 | h1096
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1097 | h1097
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1098 | h1098
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1099 | h1099
                  · linarith only [h10, h1096, h1099, h712, h986, hc12, hc23, hlam, hphi]
                  · linarith only [h10, h1098, h1099, h712, hc12, hc24, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1102 | h1102
                  · linarith only [h0, h10, h1096, h1102, h4, h712, h986, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h1bigk with h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      rcases p1104_3 (m.d 0 1) (by simp) with h1106 | h1106
                      · rcases p1104_3 (m.d 1 2) (by simp) with h1107 | h1107
                        · linarith only [h1107, hlam, p1104_0]
                        · rcases p1104_3 (m.d 1 3) (by simp) with h1109 | h1109
                          · linarith only [h1, h1109, hlam]
                          · linarith only [h10, h1109, hlam]
                      · linarith only [h1106, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      rcases p1104_3 (m.d 0 1) (by simp) with h1113 | h1113
                      · rcases p1104_3 (m.d 1 2) (by simp) with h1114 | h1114
                        · linarith only [h0, h1114, hlam]
                        · rcases p1104_3 (m.d 1 3) (by simp) with h1116 | h1116
                          · linarith only [h1116, hlam, p1104_0]
                          · rcases p1104_3 (m.d 1 4) (by simp) with h1118 | h1118
                            · linarith only [h1118, h2, hlam]
                            · linarith only [h1118, h712, hlam]
                      · linarith only [h1113, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      rcases p1104_3 (m.d 0 1) (by simp) with h1122 | h1122
                      · rcases p1104_3 (m.d 1 2) (by simp) with h1123 | h1123
                        · linarith only [h0, h1123, hlam]
                        · rcases p1104_3 (m.d 1 3) (by simp) with h1125 | h1125
                          · linarith only [h1, h1125, hlam]
                          · rcases p1104_3 (m.d 1 4) (by simp) with h1127 | h1127
                            · linarith only [h1127, hlam, p1104_0]
                            · rcases p1104_3 (m.d 1 5) (by simp) with h1129 | h1129
                              · linarith only [h1129, h3, hlam]
                              · linarith only [h1129, h986, hlam]
                      · linarith only [h1122, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      rcases p1104_3 (m.d 0 1) (by simp) with h1133 | h1133
                      · rcases p1104_3 (m.d 1 2) (by simp) with h1134 | h1134
                        · linarith only [h0, h1134, hlam]
                        · rcases p1104_3 (m.d 1 3) (by simp) with h1136 | h1136
                          · linarith only [h1, h1136, hlam]
                          · rcases p1104_3 (m.d 1 4) (by simp) with h1138 | h1138
                            · linarith only [h1138, h2, hlam]
                            · rcases p1104_3 (m.d 1 5) (by simp) with h1140 | h1140
                              · linarith only [h1140, hlam, p1104_0]
                              · rcases h1emin with h1142 | h1142 | h1142 | h1142 | h1142
                                · rcases h5bigk with h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [hlam, p1143_0]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    rcases p1143_3 (m.d 0 5) (by simp) with h1145 | h1145
                                    · rcases p1143_3 (m.d 1 5) (by simp) with h1146 | h1146
                                      · linarith only [h1146, h3, hlam]
                                      · rcases p1143_3 (m.d 2 5) (by simp) with h1148 | h1148
                                        · linarith only [h1148, h6, hlam]
                                        · linarith only [h1148, h661, hlam]
                                    · linarith only [h1145, h3, hlam]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    rcases p1143_3 (m.d 0 5) (by simp) with h1152 | h1152
                                    · rcases p1143_3 (m.d 1 5) (by simp) with h1153 | h1153
                                      · linarith only [h1153, h3, hlam]
                                      · rcases p1143_3 (m.d 2 5) (by simp) with h1155 | h1155
                                        · linarith only [h1155, h6, hlam]
                                        · rcases p1143_3 (m.d 3 5) (by simp) with h1157 | h1157
                                          · linarith only [h1157, h8, hlam]
                                          · rcases p1143_3 (m.d 4 5) (by simp) with h1159 | h1159
                                            · linarith only [h1159, h9, hlam]
                                            · linarith only [h1098, h1159, hlam]
                                    · linarith only [h1152, h6, hlam]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    rcases p1143_3 (m.d 0 5) (by simp) with h1163 | h1163
                                    · rcases p1143_3 (m.d 1 5) (by simp) with h1164 | h1164
                                      · linarith only [h1164, h3, hlam]
                                      · rcases p1143_3 (m.d 2 5) (by simp) with h1166 | h1166
                                        · linarith only [h1166, h6, hlam]
                                        · linarith only [h1097, h1166, hlam]
                                    · linarith only [h1163, h8, hlam]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h10, h1096, h1098, h712, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1143_1]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h3, hlam, p1143_0]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [hlam, p1143_0]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h661, hlam, p1143_0]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h937, hlam, p1143_1]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h986, hlam, p1143_1]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h6, hlam, p1143_1]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    rcases p1143_3 (m.d 0 5) (by simp) with h1177 | h1177
                                    · rcases p1143_3 (m.d 1 5) (by simp) with h1178 | h1178
                                      · linarith only [h1178, h661, hlam]
                                      · rcases p1143_3 (m.d 2 5) (by simp) with h1180 | h1180
                                        · rcases p1143_3 (m.d 3 5) (by simp) with h1181 | h1181
                                          · linarith only [h1097, h1181, hlam]
                                          · linarith only [h1181, h937, hlam]
                                        · linarith only [h1180, h661, hlam]
                                    · linarith only [h1177, h3, hlam]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [hlam, p1143_0]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h10, h937, hc12, hc25, hlam, hphi, p1143_1]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h1098, hlam, p1143_1]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h8, hlam, p1143_0]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h0, h10, h1097, h4, h712, h986, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1143_1]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h1097, hlam, p1143_0]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [hlam, p1143_0]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h1102, hlam, p1143_1]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h9, hlam, p1143_0]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    rcases p1143_3 (m.d 0 5) (by simp) with h1195 | h1195
                                    · rcases p1143_3 (m.d 1 5) (by simp) with h1196 | h1196
                                      · linarith only [h1196, h986, hlam]
                                      · rcases p1143_3 (m.d 2 5) (by simp) with h1198 | h1198
                                        · linarith only [h1098, h1198, hlam]
                                        · linarith only [h1198, h661, hlam]
                                    · linarith only [h1195, h3, hlam]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h0, h4, h661, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1143_1]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [h0, h10, h4, h7, h9, h937, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1143_1]
                                  · have p1143_0 := h1143c.1
                                    have p1143_1 := h1143c.2.1
                                    have p1143_2 := h1143c.2.2.1
                                    have p1143_3 := h1143c.2.2.2
                                    linarith only [hlam, p1143_0]
                                · linarith only [h10, h1096, h1142, h712, hc24, hlam, ht12]
                                · linarith only [h1096, h1142, h712, hc24, hlam, ht12]
                                · linarith only [h1142, h986, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1104_1]
                                · linarith only [h1142, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1104_1]
                      · linarith only [h1133, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h10, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h555, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h661, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h1, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h1096, h1098, h712, hc12, hc25, hlam, hphi, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h712, hlam, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h937, hlam, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h2, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, h1096, h5, h712, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h986, hlam, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h3, hlam, p1104_0]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, h6, h661, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, h10, h4, h8, h937, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [h0, h4, h7, h9, h986, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1104_1]
                    · have p1104_0 := h1104c.1
                      have p1104_1 := h1104c.2.1
                      have p1104_2 := h1104c.2.2.1
                      have p1104_3 := h1104c.2.2.2
                      linarith only [hlam, p1104_0]
              · linarith only [h0, h10, h1096, h1097, h4, h712, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1231 | h1231
              · linarith only [h10, h1096, h1231, h937, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1233 | h1233
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1234 | h1234
                  · rcases h1bigk with h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      rcases p1235_3 (m.d 0 1) (by simp) with h1237 | h1237
                      · rcases p1235_3 (m.d 1 2) (by simp) with h1238 | h1238
                        · linarith only [h1238, hlam, p1235_0]
                        · rcases p1235_3 (m.d 1 3) (by simp) with h1240 | h1240
                          · linarith only [h1, h1240, hlam]
                          · linarith only [h10, h1240, hlam]
                      · linarith only [h1237, hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      rcases p1235_3 (m.d 0 1) (by simp) with h1244 | h1244
                      · rcases p1235_3 (m.d 1 2) (by simp) with h1245 | h1245
                        · linarith only [h0, h1245, hlam]
                        · rcases p1235_3 (m.d 1 3) (by simp) with h1247 | h1247
                          · linarith only [h1247, hlam, p1235_0]
                          · rcases p1235_3 (m.d 1 4) (by simp) with h1249 | h1249
                            · linarith only [h1249, h2, hlam]
                            · linarith only [h1249, h712, hlam]
                      · linarith only [h1244, hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      rcases p1235_3 (m.d 0 1) (by simp) with h1253 | h1253
                      · rcases p1235_3 (m.d 1 2) (by simp) with h1254 | h1254
                        · linarith only [h0, h1254, hlam]
                        · rcases p1235_3 (m.d 1 3) (by simp) with h1256 | h1256
                          · linarith only [h1, h1256, hlam]
                          · rcases p1235_3 (m.d 1 4) (by simp) with h1258 | h1258
                            · linarith only [h1258, hlam, p1235_0]
                            · rcases p1235_3 (m.d 1 5) (by simp) with h1260 | h1260
                              · linarith only [h1260, h3, hlam]
                              · linarith only [h1260, h986, hlam]
                      · linarith only [h1253, hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      rcases p1235_3 (m.d 0 1) (by simp) with h1264 | h1264
                      · rcases p1235_3 (m.d 1 2) (by simp) with h1265 | h1265
                        · linarith only [h0, h1265, hlam]
                        · rcases p1235_3 (m.d 1 3) (by simp) with h1267 | h1267
                          · linarith only [h1, h1267, hlam]
                          · rcases p1235_3 (m.d 1 4) (by simp) with h1269 | h1269
                            · linarith only [h1269, h2, hlam]
                            · rcases p1235_3 (m.d 1 5) (by simp) with h1271 | h1271
                              · linarith only [h1271, hlam, p1235_0]
                              · rcases h1emin with h1273 | h1273 | h1273 | h1273 | h1273
                                · rcases h5bigk with h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [hlam, p1274_0]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    rcases p1274_3 (m.d 0 5) (by simp) with h1276 | h1276
                                    · rcases p1274_3 (m.d 1 5) (by simp) with h1277 | h1277
                                      · linarith only [h1277, h3, hlam]
                                      · rcases p1274_3 (m.d 2 5) (by simp) with h1279 | h1279
                                        · linarith only [h1279, h6, hlam]
                                        · linarith only [h1279, h661, hlam]
                                    · linarith only [h1276, h3, hlam]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    rcases p1274_3 (m.d 0 5) (by simp) with h1283 | h1283
                                    · rcases p1274_3 (m.d 1 5) (by simp) with h1284 | h1284
                                      · linarith only [h1284, h3, hlam]
                                      · rcases p1274_3 (m.d 2 5) (by simp) with h1286 | h1286
                                        · linarith only [h1286, h6, hlam]
                                        · rcases p1274_3 (m.d 3 5) (by simp) with h1288 | h1288
                                          · linarith only [h1288, h8, hlam]
                                          · linarith only [h1231, h1288, hlam]
                                    · linarith only [h1283, h6, hlam]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h0, h10, h1231, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1274_1]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    rcases p1274_3 (m.d 0 5) (by simp) with h1293 | h1293
                                    · rcases p1274_3 (m.d 1 5) (by simp) with h1294 | h1294
                                      · linarith only [h1294, h3, hlam]
                                      · rcases p1274_3 (m.d 2 5) (by simp) with h1296 | h1296
                                        · linarith only [h1296, h6, hlam]
                                        · linarith only [h1233, h1296, hlam]
                                    · linarith only [h1293, h9, hlam]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h3, hlam, p1274_0]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [hlam, p1274_0]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h661, hlam, p1274_0]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h937, hlam, p1274_1]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h986, hlam, p1274_1]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h6, hlam, p1274_1]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    rcases p1274_3 (m.d 0 5) (by simp) with h1306 | h1306
                                    · rcases p1274_3 (m.d 1 5) (by simp) with h1307 | h1307
                                      · linarith only [h1307, h661, hlam]
                                      · rcases p1274_3 (m.d 2 5) (by simp) with h1309 | h1309
                                        · rcases p1274_3 (m.d 3 5) (by simp) with h1310 | h1310
                                          · rcases p1274_3 (m.d 4 5) (by simp) with h1311 | h1311
                                            · linarith only [h1233, h1311, hlam]
                                            · linarith only [h1311, h986, hlam]
                                          · linarith only [h1310, h937, hlam]
                                        · linarith only [h1309, h661, hlam]
                                    · linarith only [h1306, h3, hlam]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [hlam, p1274_0]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h1231, hlam, p1274_1]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h10, h712, h986, hc12, hc25, hlam, hphi, p1274_1]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h8, hlam, p1274_0]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    rcases p1274_3 (m.d 0 5) (by simp) with h1321 | h1321
                                    · rcases p1274_3 (m.d 1 5) (by simp) with h1322 | h1322
                                      · linarith only [h1322, h937, hlam]
                                      · rcases p1274_3 (m.d 2 5) (by simp) with h1324 | h1324
                                        · linarith only [h1231, h1324, hlam]
                                        · linarith only [h1324, h661, hlam]
                                    · linarith only [h1321, h3, hlam]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h0, h1234, h4, h661, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1274_1]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [hlam, p1274_0]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h0, h10, h1234, h4, h7, h712, h986, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1274_1]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h9, hlam, p1274_0]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h0, h10, h1096, h1233, h4, h7, h712, h986, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1274_1]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h1233, hlam, p1274_0]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [h1234, hlam, p1274_0]
                                  · have p1274_0 := h1274c.1
                                    have p1274_1 := h1274c.2.1
                                    have p1274_2 := h1274c.2.2.1
                                    have p1274_3 := h1274c.2.2.2
                                    linarith only [hlam, p1274_0]
                                · linarith only [h10, h1273, hc23, hlam, ht12]
                                · linarith only [h1273, h712, h986, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1235_1]
                                · linarith only [h1273, h986, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1235_1]
                                · linarith only [h1273, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1235_1]
                      · linarith only [h1264, hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h0, hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h10, hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h555, hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h661, hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h1, hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1235_1]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h712, hlam, p1235_1]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h937, hlam, p1235_1]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h2, hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h0, h1096, h4, h555, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1235_1]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h0, h1096, h4, h555, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1235_1]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h986, hlam, p1235_1]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h3, hlam, p1235_0]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h0, h6, h661, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1235_1]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h0, h10, h1234, h4, h7, h937, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1235_1]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [h0, h1234, h4, h7, h937, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1235_1]
                    · have p1235_0 := h1235c.1
                      have p1235_1 := h1235c.2.1
                      have p1235_2 := h1235c.2.2.1
                      have p1235_3 := h1235c.2.2.2
                      linarith only [hlam, p1235_0]
                  · linarith only [h1096, h1233, h1234, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1362 | h1362
                  · linarith only [h0, h10, h1096, h1233, h1362, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h10, h1096, h1362, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
