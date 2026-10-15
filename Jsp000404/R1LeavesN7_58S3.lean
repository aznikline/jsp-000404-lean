import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_58S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3592000 in
set_option maxHeartbeats 3592000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1elo := hb1.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h602 | h602
  · rcases m.htr 0 4 5 (by decide) (by decide) with h603 | h603
    · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
      · rcases m.htr 1 2 5 (by decide) (by decide) with h605 | h605
        · linarith only [h1, h2, h605, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h607 | h607
          · rcases m.htr 1 3 5 (by decide) (by decide) with h608 | h608
            · linarith only [h604, h605, h608, hlam]
            · linarith only [h602, h603, h607, h608, hc34, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
            · linarith only [h604, h605, h607, h611, hc23, hlam, hphi, ht34, u4elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h613 | h613
              · rcases m.htr 2 3 4 (by decide) (by decide) with h614 | h614
                · linarith only [h1, h604, h605, h614, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h616 | h616
                  · linarith only [h0, h604, h605, h611, h613, h616, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h2, h602, h616, hlam]
              · linarith only [h603, h613, hc14, hlam, hphi, u4elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h620 | h620
        · linarith only [h2, h604, h620, hc02, hc23, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h622 | h622
          · rcases m.htr 1 3 5 (by decide) (by decide) with h623 | h623
            · rcases m.htr 1 4 5 (by decide) (by decide) with h624 | h624
              · rcases m.htr 2 3 4 (by decide) (by decide) with h625 | h625
                · rcases m.htr 2 3 5 (by decide) (by decide) with h626 | h626
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h627 | h627
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h628 | h628
                      · rcases h5bigk with h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [hlam, p629_0]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h2, h627, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p629_1, u4elo2]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h2, hlam, p629_0]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h2, h627, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p629_1, u4elo2]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h2, h627, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p629_1, u4elo2]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h1, hlam, p629_0]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [hlam, p629_0]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h620, hlam, p629_0]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p629_1, u1elo4]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h0, h624, hc45, hlam, hphi, ht01, ht0b, ht5b, p629_1, u1elo0]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h627, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p629_1, u4elo2]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h627, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p629_1, u4elo2]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [hlam, p629_0]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h627, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p629_1, u4elo2]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h627, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p629_1, u4elo2]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h602, hlam, p629_1]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h623, hlam, p629_1]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h626, hlam, p629_0]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [hlam, p629_0]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h602, hc03, hc45, hlam, hphi, ht0b, ht5b, p629_1]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h603, hlam, p629_1]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h624, hlam, p629_1]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h627, hlam, p629_1]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [h628, hlam, p629_1]
                        · have p629_0 := h629c.1
                          have p629_1 := h629c.2.1
                          have p629_2 := h629c.2.2.1
                          have p629_3 := h629c.2.2.2
                          linarith only [hlam, p629_0]
                      · linarith only [h603, h628, hc34, hlam, hphi, u4elo0]
                    · linarith only [h0, h624, h627, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h604, h623, h626, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h604, h625, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h603, h624, hc14, hlam, hphi, u4elo0]
            · linarith only [h602, h603, h622, h623, hc34, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h661 | h661
            · rcases m.htr 1 4 5 (by decide) (by decide) with h662 | h662
              · rcases m.htr 2 3 4 (by decide) (by decide) with h663 | h663
                · rcases m.htr 2 3 5 (by decide) (by decide) with h664 | h664
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h665 | h665
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h666 | h666
                      · rcases h5bigk with h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [hlam, p667_0]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h2, h665, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p667_1, u4elo2]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h2, hlam, p667_0]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h2, h665, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p667_1, u4elo2]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h2, h665, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p667_1, u4elo2]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h1, hlam, p667_0]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [hlam, p667_0]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h620, hlam, p667_0]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h666, hc45, hlam, hphi, ht01, ht0b, ht5b, p667_1, u1elo4]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h622, h661, h663, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p667_1, u4elo2]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h665, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p667_1, u4elo2]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h665, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p667_1, u4elo2]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [hlam, p667_0]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h665, h666, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p667_1, u4elo2]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h665, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p667_1, u4elo2]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h602, hlam, p667_1]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h661, hlam, p667_1]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h664, hlam, p667_0]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [hlam, p667_0]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h602, hc03, hc45, hlam, hphi, ht0b, ht5b, p667_1]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h603, hlam, p667_1]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h662, hlam, p667_1]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h665, hlam, p667_1]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [h666, hlam, p667_1]
                        · have p667_0 := h667c.1
                          have p667_1 := h667c.2.1
                          have p667_2 := h667c.2.2.1
                          have p667_3 := h667c.2.2.2
                          linarith only [hlam, p667_0]
                      · linarith only [h622, h666, hc13, hlam, hphi, ht34, u4elo4]
                    · linarith only [h662, h665, hc24, hlam, hphi, u4elo1]
                  · linarith only [h622, h661, h663, h664, hlam]
                · linarith only [h604, h663, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h603, h662, hc14, hlam, hphi, u4elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h698 | h698
              · rcases m.htr 2 3 4 (by decide) (by decide) with h699 | h699
                · rcases m.htr 2 3 5 (by decide) (by decide) with h700 | h700
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h701 | h701
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h702 | h702
                      · rcases h5bigk with h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [hlam, p703_0]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h1, h661, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p703_1, u1elo0]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h2, hlam, p703_0]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h661, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p703_1]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h603, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p703_1, u4elo0]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h1, hlam, p703_0]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [hlam, p703_0]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h620, hlam, p703_0]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h661, hlam, p703_0]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p703_1, u1elo4]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h2, hc02, hc25, hlam, hphi, p703_1]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h620, hc12, hc25, hlam, hphi, p703_1]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [hlam, p703_0]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h604, h661, h700, hc12, hc23, hlam, hphi, p703_1]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h701, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p703_1, u4elo2]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h602, hlam, p703_1]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h604, h661, hc12, hc35, hlam, hphi, ht23, p703_1]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h700, hlam, p703_0]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [hlam, p703_0]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h2, h602, h701, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p703_1, u4elo2]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h603, hlam, p703_1]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h698, hlam, p703_1]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h701, hlam, p703_1]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [h702, hlam, p703_1]
                        · have p703_0 := h703c.1
                          have p703_1 := h703c.2.1
                          have p703_2 := h703c.2.2.1
                          have p703_3 := h703c.2.2.2
                          linarith only [hlam, p703_0]
                      · linarith only [h698, h702, hc34, hlam, hphi, u4elo1]
                    · linarith only [h0, h698, h701, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h602, h603, h604, h700, hc12, hlam, hphi, ht23, ht34, u4elo0]
                · linarith only [h604, h699, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h603, h698, hc14, hlam, hphi, u4elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h734 | h734
      · rcases m.htr 1 2 5 (by decide) (by decide) with h735 | h735
        · linarith only [h1, h2, h735, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h737 | h737
          · rcases m.htr 1 3 5 (by decide) (by decide) with h738 | h738
            · linarith only [h734, h735, h738, hlam]
            · linarith only [h602, h603, h737, h738, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h741 | h741
            · linarith only [h734, h735, h737, h741, hc23, hlam, hphi, ht34, u4elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h743 | h743
              · linarith only [h0, h603, h743, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h745 | h745
                · linarith only [h1, h734, h735, h745, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h747 | h747
                  · linarith only [h1, h734, h735, h741, h747, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h2, h602, h747, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h750 | h750
        · linarith only [h2, h734, h750, hc02, hc23, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h752 | h752
          · rcases m.htr 1 3 5 (by decide) (by decide) with h753 | h753
            · rcases m.htr 1 4 5 (by decide) (by decide) with h754 | h754
              · linarith only [h0, h603, h754, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h756 | h756
                · rcases m.htr 2 3 5 (by decide) (by decide) with h757 | h757
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h758 | h758
                    · linarith only [h603, h758, hc04, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h760 | h760
                      · linarith only [h0, h750, h752, h758, h760, hc12, hlam, hphi, ht23, ht34, u4elo0]
                      · rcases h5bigk with h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h1, h753, hc35, hlam, hphi, ht01, ht0b, ht5b, p762_1, u1elo0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h2, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h2, h758, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p762_1, u4elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h603, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h1, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h750, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p762_1, u1elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h754, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h758, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p762_1, u4elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h758, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p762_1, u4elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h758, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p762_1, u4elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h758, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h602, hlam, p762_1]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h753, hlam, p762_1]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h757, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h760, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h603, hc04, hlam, hphi, p762_1, u4elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h750, hc12, hlam, hphi, ht23, ht34, p762_1, u4elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p762_1, u4elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p762_1, u4elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hlam, p762_0]
                  · linarith only [h602, h603, h734, h757, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h734, h752, h756, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · linarith only [h602, h603, h752, h753, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h791 | h791
            · rcases m.htr 1 4 5 (by decide) (by decide) with h792 | h792
              · linarith only [h0, h603, h792, hlam]
              · linarith only [h752, h791, h792, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h795 | h795
              · linarith only [h0, h603, h795, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h797 | h797
                · rcases m.htr 2 3 5 (by decide) (by decide) with h798 | h798
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h799 | h799
                    · linarith only [h603, h799, hc04, hlam, hphi, u4elo2]
                    · linarith only [h734, h752, h797, h799, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h734, h752, h797, h798, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h734, h797, hc12, hlam, hphi, ht23, ht34, u4elo3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h804 | h804
    · rcases m.htr 1 2 3 (by decide) (by decide) with h805 | h805
      · rcases m.htr 1 2 5 (by decide) (by decide) with h806 | h806
        · linarith only [h1, h2, h806, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h808 | h808
          · rcases m.htr 1 3 5 (by decide) (by decide) with h809 | h809
            · linarith only [h1, h602, h805, h806, h809, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h811 | h811
              · linarith only [h805, h806, h808, h811, hlam]
              · linarith only [h804, h811, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h814 | h814
            · linarith only [h602, h808, h814, hc03, hlam, hphi, ht34, u4elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h816 | h816
              · rcases m.htr 2 3 4 (by decide) (by decide) with h817 | h817
                · linarith only [h805, h808, h817, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h819 | h819
                  · linarith only [h1, h602, h805, h806, h819, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h821 | h821
                    · linarith only [h805, h806, h821, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h816, h821, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h804, h816, hc14, hlam, hphi, u4elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h825 | h825
        · linarith only [h2, h805, h825, hc02, hc23, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h827 | h827
          · rcases m.htr 1 3 5 (by decide) (by decide) with h828 | h828
            · linarith only [h1, h602, h828, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h830 | h830
              · linarith only [h827, h828, h830, hlam]
              · linarith only [h804, h830, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h833 | h833
            · linarith only [h602, h827, h833, hc03, hlam, hphi, ht34, u4elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h835 | h835
              · rcases m.htr 2 3 4 (by decide) (by decide) with h836 | h836
                · rcases m.htr 2 3 5 (by decide) (by decide) with h837 | h837
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h838 | h838
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h839 | h839
                      · rcases h5bigk with h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [hlam, p840_0]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h1, h805, h833, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p840_1, u1elo0]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h2, hlam, p840_0]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h602, hlam, p840_0]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h602, h837, h838, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p840_1, u4elo2]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h1, hlam, p840_0]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [hlam, p840_0]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h825, hlam, p840_0]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h833, hlam, p840_0]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p840_1, u1elo4]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h838, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p840_1, u4elo2]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h838, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p840_1, u4elo2]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [hlam, p840_0]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h838, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p840_1, u4elo2]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h838, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p840_1, u4elo2]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h1, h805, h833, hc12, hc35, hlam, hphi, ht23, p840_1]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h805, h833, hc12, hc35, hlam, hphi, ht23, p840_1]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h837, hlam, p840_0]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [hlam, p840_0]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h837, h838, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p840_1, u4elo2]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h804, hlam, p840_1]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h835, hlam, p840_1]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h838, hlam, p840_1]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [h839, hlam, p840_1]
                        · have p840_0 := h840c.1
                          have p840_1 := h840c.2.1
                          have p840_2 := h840c.2.2.1
                          have p840_3 := h840c.2.2.2
                          linarith only [hlam, p840_0]
                      · linarith only [h835, h839, hc34, hlam, hphi, u4elo1]
                    · linarith only [h0, h835, h838, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h805, h827, h836, h837, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h805, h836, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h804, h835, hc14, hlam, hphi, u4elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h871 | h871
      · rcases m.htr 1 2 5 (by decide) (by decide) with h872 | h872
        · linarith only [h1, h2, h872, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h874 | h874
          · rcases m.htr 1 3 5 (by decide) (by decide) with h875 | h875
            · linarith only [h1, h602, h871, h872, h875, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h877 | h877
              · linarith only [h804, h877, hc04, hlam, hphi, u4elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h879 | h879
                · linarith only [h1, h871, h872, h879, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h874, h875, h879, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h882 | h882
            · linarith only [h0, h602, h804, h874, h882, hc03, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h884 | h884
              · linarith only [h0, h804, h884, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h886 | h886
                · linarith only [h1, h871, h872, h886, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h888 | h888
                  · linarith only [h1, h602, h871, h872, h888, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h890 | h890
                    · linarith only [h804, h890, hc04, hlam, hphi, u4elo2]
                    · linarith only [h871, h872, h890, hc23, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h893 | h893
        · linarith only [h2, h871, h893, hc02, hc23, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h895 | h895
          · rcases m.htr 1 3 5 (by decide) (by decide) with h896 | h896
            · linarith only [h1, h602, h896, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h898 | h898
              · linarith only [h0, h804, h898, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h900 | h900
                · rcases m.htr 2 3 5 (by decide) (by decide) with h901 | h901
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h902 | h902
                    · linarith only [h804, h902, hc04, hlam, hphi, u4elo2]
                    · linarith only [h895, h896, h901, h902, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h905 | h905
                    · linarith only [h804, h905, hc04, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h907 | h907
                      · linarith only [h1, h2, h895, h896, h905, h907, hlam]
                      · linarith only [h895, h896, h907, hc34, hlam, hphi, u4elo4]
                · linarith only [h1, h871, h895, h896, h900, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h911 | h911
            · linarith only [h0, h602, h804, h895, h911, hc03, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h913 | h913
              · linarith only [h0, h804, h913, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h915 | h915
                · rcases m.htr 2 3 5 (by decide) (by decide) with h916 | h916
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h917 | h917
                    · linarith only [h804, h917, hc04, hlam, hphi, u4elo2]
                    · linarith only [h871, h895, h915, h917, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h871, h895, h915, h916, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h871, h915, hc12, hlam, hphi, ht23, ht34, u4elo3]

set_option maxHeartbeats 3592000 in
set_option maxHeartbeats 3592000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1elo := hb1.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2
  · exact r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2

set_option maxHeartbeats 3592000 in
set_option maxHeartbeats 3592000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h1 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1elo := hb1.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h922 | h922
  · rcases m.htr 0 3 5 (by decide) (by decide) with h923 | h923
    · rcases m.htr 0 4 5 (by decide) (by decide) with h924 | h924
      · linarith only [h0, h1, h924, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h926 | h926
        · rcases m.htr 1 2 5 (by decide) (by decide) with h927 | h927
          · rcases m.htr 1 3 4 (by decide) (by decide) with h928 | h928
            · rcases m.htr 1 3 5 (by decide) (by decide) with h929 | h929
              · rcases m.htr 1 4 5 (by decide) (by decide) with h930 | h930
                · linarith only [h0, h1, h924, h929, h930, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · linarith only [h0, h1, h928, h930, hc34, hlam, hphi, u4elo4]
              · linarith only [h923, h924, h928, h929, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h934 | h934
              · linarith only [h0, h1, h928, h934, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
              · linarith only [h0, h1, h923, h924, h926, h928, h934, hc23, hlam, hphi, ht34, u4elo4]
          · linarith only [h922, h924, h926, h927, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h938 | h938
          · rcases m.htr 1 3 4 (by decide) (by decide) with h939 | h939
            · rcases m.htr 1 3 5 (by decide) (by decide) with h940 | h940
              · rcases m.htr 1 4 5 (by decide) (by decide) with h941 | h941
                · linarith only [h0, h1, h924, h926, h938, h941, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · linarith only [h0, h1, h939, h941, hc34, hlam, hphi, u4elo4]
              · linarith only [h1, h923, h926, h938, h940, hlam]
            · linarith only [h0, h1, h926, h938, h939, hc14, hlam, hphi, u4elo3]
          · linarith only [h0, h1, h922, h924, h938, hc14, hlam, hphi, u4elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h947 | h947
      · linarith only [h0, h1, h947, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h949 | h949
        · rcases m.htr 1 2 5 (by decide) (by decide) with h950 | h950
          · rcases m.htr 1 3 4 (by decide) (by decide) with h951 | h951
            · rcases m.htr 1 3 5 (by decide) (by decide) with h952 | h952
              · rcases m.htr 1 4 5 (by decide) (by decide) with h953 | h953
                · linarith only [h0, h1, h923, h947, h952, h953, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · linarith only [h0, h1, h951, h953, hc34, hlam, hphi, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h956 | h956
                · linarith only [h0, h1, h956, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                · linarith only [h0, h1, h951, h956, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h959 | h959
              · linarith only [h0, h1, h950, h951, h959, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h961 | h961
                · linarith only [h0, h1, h950, h961, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · linarith only [h0, h1, h949, h951, h961, hc23, hlam, hphi, ht34, u4elo4]
          · linarith only [h922, h947, h949, h950, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h965 | h965
          · rcases m.htr 1 3 4 (by decide) (by decide) with h966 | h966
            · rcases m.htr 1 3 5 (by decide) (by decide) with h967 | h967
              · rcases m.htr 1 4 5 (by decide) (by decide) with h968 | h968
                · linarith only [h0, h1, h949, h965, h968, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h1, h966, h968, hc34, hlam, hphi, u4elo4]
              · linarith only [h949, h965, h967, hlam]
            · linarith only [h1, h949, h965, h966, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · linarith only [h0, h1, h922, h947, h965, hc14, hlam, hphi, u4elo4]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h974 | h974
    · rcases m.htr 0 4 5 (by decide) (by decide) with h975 | h975
      · linarith only [h0, h1, h975, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h977 | h977
        · rcases m.htr 1 2 5 (by decide) (by decide) with h978 | h978
          · rcases m.htr 1 3 4 (by decide) (by decide) with h979 | h979
            · rcases m.htr 1 3 5 (by decide) (by decide) with h980 | h980
              · rcases m.htr 1 4 5 (by decide) (by decide) with h981 | h981
                · linarith only [h0, h1, h975, h980, h981, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · linarith only [h0, h1, h979, h981, hc34, hlam, hphi, u4elo4]
              · linarith only [h922, h974, h978, h979, h980, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h985 | h985
              · linarith only [h0, h1, h979, h985, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
              · linarith only [h1, h922, h974, h978, h985, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h988 | h988
            · rcases m.htr 1 3 5 (by decide) (by decide) with h989 | h989
              · linarith only [h977, h978, h989, hlam]
              · linarith only [h974, h975, h988, h989, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h992 | h992
              · linarith only [h0, h1, h988, h992, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
              · linarith only [h0, h1, h974, h975, h988, h992, hc13, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h995 | h995
          · linarith only [h922, h977, h995, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h997 | h997
            · rcases m.htr 1 3 5 (by decide) (by decide) with h998 | h998
              · rcases m.htr 1 4 5 (by decide) (by decide) with h999 | h999
                · linarith only [h0, h1, h975, h999, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                · linarith only [h0, h1, h999, hc14, hlam, hphi, u4elo4]
              · linarith only [h974, h975, h997, h998, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1003 | h1003
              · linarith only [h0, h1, h1003, h997, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
              · linarith only [h0, h1, h1003, h974, h975, h977, h997, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1006 | h1006
      · linarith only [h0, h1, h1006, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1008 | h1008
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1009 | h1009
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1010 | h1010
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1011 | h1011
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1012 | h1012
                · linarith only [h0, h1, h1006, h1008, h1011, h1012, h974, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · linarith only [h0, h1, h1010, h1012, hc34, hlam, hphi, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1015 | h1015
                · linarith only [h0, h1, h1015, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                · linarith only [h0, h1, h1015, hc14, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1018 | h1018
              · linarith only [h0, h1, h1010, h1018, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1020 | h1020
                · linarith only [h0, h1, h1009, h1020, h922, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · linarith only [h0, h1, h1010, h1020, hc13, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1023 | h1023
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1024 | h1024
              · linarith only [h1008, h1009, h1024, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1026 | h1026
                · linarith only [h0, h1, h1026, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                · linarith only [h0, h1, h1026, hc14, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1029 | h1029
              · linarith only [h0, h1, h1023, h1029, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1031 | h1031
                · linarith only [h0, h1, h1031, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                · linarith only [h0, h1, h1008, h1023, h1031, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1034 | h1034
          · linarith only [h1008, h1034, h922, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1036 | h1036
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1037 | h1037
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1038 | h1038
                · linarith only [h0, h1, h1037, h1038, h974, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · linarith only [h0, h1, h1038, hc14, hlam, hphi, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1041 | h1041
                · linarith only [h0, h1, h1041, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                · linarith only [h0, h1, h1036, h1041, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1044 | h1044
              · linarith only [h0, h1, h1036, h1044, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1046 | h1046
                · linarith only [h0, h1, h1046, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                · linarith only [h0, h1, h1008, h1036, h1046, hc12, hlam, hphi, ht23, ht34, u4elo4]

set_option maxHeartbeats 3592000 in
set_option maxHeartbeats 3592000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1elo := hb1.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x0_x0 m hb1 hb2 hb4 hb5 h0 h1
  · exact r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x0_x1 m hb1 hb2 hb4 hb5 h0 h1

end R2N4
