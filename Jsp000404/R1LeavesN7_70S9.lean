import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_70S8

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_21_15_M_LI_L_0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h1bigk := hb1.2.2.2
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h571 | h571
  · rcases m.htr 0 1 4 (by decide) (by decide) with h572 | h572
    · rcases m.htr 0 1 5 (by decide) (by decide) with h573 | h573
      · rcases m.htr 1 2 3 (by decide) (by decide) with h574 | h574
        · rcases m.htr 1 2 5 (by decide) (by decide) with h575 | h575
          · rcases m.htr 1 3 4 (by decide) (by decide) with h576 | h576
            · linarith only [h0, h571, h576, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h578 | h578
              · linarith only [h0, h572, h576, h578, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h580 | h580
                · linarith only [h0, h572, h580, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h582 | h582
                  · linarith only [h574, h576, h582, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h584 | h584
                    · linarith only [h574, h578, h584, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h586 | h586
                      · rcases h1bigk with h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h0, hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p587_1, u1elo1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p587_1, u1elo1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p587_1, u1elo1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [hc01, hlam, hphi, p587_1, u1elo1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          rcases p587_3 (m.d 0 1) (by simp) with h595 | h595
                          · linarith only [h0, h595, hlam]
                          · linarith only [h571, h595, hlam]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          rcases p587_3 (m.d 0 1) (by simp) with h598 | h598
                          · linarith only [h0, h598, hlam]
                          · linarith only [h572, h598, hlam]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          rcases p587_3 (m.d 0 1) (by simp) with h601 | h601
                          · linarith only [h0, h601, hlam]
                          · linarith only [h573, h601, hlam]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h571, hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h574, hlam, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h576, hlam, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h578, hlam, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h572, hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h580, h586, hc12, hc34, hlam, hphi, ht23, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h580, h586, hc13, hc34, hlam, hphi, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h580, hlam, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h573, hlam, p587_0]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h575, hlam, p587_1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h0, h573, h574, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p587_1, u1elo1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [h0, h573, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p587_1, u1elo1]
                        · have p587_0 := h587c.1
                          have p587_1 := h587c.2.1
                          have p587_2 := h587c.2.2.1
                          have p587_3 := h587c.2.2.2
                          linarith only [hlam, p587_0]
                      · linarith only [h574, h576, h586, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h0, h575, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h571, h574, hlam]
      · linarith only [h571, h573, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h623 | h623
      · rcases m.htr 1 2 3 (by decide) (by decide) with h624 | h624
        · rcases m.htr 1 2 5 (by decide) (by decide) with h625 | h625
          · rcases m.htr 1 3 4 (by decide) (by decide) with h626 | h626
            · linarith only [h0, h571, h626, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h628 | h628
              · linarith only [h0, h571, h628, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h630 | h630
                · rcases m.htr 2 3 4 (by decide) (by decide) with h631 | h631
                  · linarith only [h572, h623, h624, h626, h628, h631, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h633 | h633
                    · linarith only [h624, h628, h633, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h635 | h635
                      · rcases h1bigk with h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [hlam, p636_0]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h0, hlam, p636_0]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p636_1, u1elo1]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h572, hlam, p636_0]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p636_1, u1elo1]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [hc01, hlam, hphi, p636_1, u1elo1]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [hlam, p636_0]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          rcases p636_3 (m.d 0 1) (by simp) with h644 | h644
                          · linarith only [h0, h644, hlam]
                          · linarith only [h571, h644, hlam]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h572, h623, h624, h628, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p636_1, u1elo1]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          rcases p636_3 (m.d 0 1) (by simp) with h648 | h648
                          · linarith only [h0, h648, hlam]
                          · linarith only [h623, h648, hlam]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h571, hlam, p636_0]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h624, hlam, p636_1]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [hlam, p636_0]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h626, hlam, p636_1]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h628, hlam, p636_1]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h623, h624, h628, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p636_1, u1elo3]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h0, h623, h624, h628, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p636_1, u1elo3]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          rcases p636_3 (m.d 0 1) (by simp) with h658 | h658
                          · linarith only [h572, h658, hlam]
                          · linarith only [h571, h658, hlam]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [hlam, p636_0]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          rcases p636_3 (m.d 0 1) (by simp) with h662 | h662
                          · linarith only [h572, h662, hlam]
                          · linarith only [h623, h662, hlam]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h623, hlam, p636_0]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h625, hlam, p636_1]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h0, h623, h624, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p636_1, u1elo1]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [h630, hlam, p636_0]
                        · have p636_0 := h636c.1
                          have p636_1 := h636c.2.1
                          have p636_2 := h636c.2.2.1
                          have p636_3 := h636c.2.2.2
                          linarith only [hlam, p636_0]
                      · linarith only [h0, h623, h626, h630, h635, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · linarith only [h572, h630, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · linarith only [h0, h571, h624, h625, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · linarith only [h0, h571, h624, hlam]
      · linarith only [h571, h623, hc13, hlam, hphi, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h675 | h675
    · rcases m.htr 0 1 5 (by decide) (by decide) with h676 | h676
      · rcases m.htr 1 2 3 (by decide) (by decide) with h677 | h677
        · rcases m.htr 1 2 5 (by decide) (by decide) with h678 | h678
          · rcases m.htr 1 3 4 (by decide) (by decide) with h679 | h679
            · rcases m.htr 1 3 5 (by decide) (by decide) with h680 | h680
              · rcases m.htr 1 4 5 (by decide) (by decide) with h681 | h681
                · linarith only [h571, h675, h677, h681, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h683 | h683
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h684 | h684
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h685 | h685
                      · linarith only [h679, h681, h685, hlam]
                      · rcases h1bigk with h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [hlam, p687_0]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h0, hlam, p687_0]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h571, hlam, p687_0]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h571, h677, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p687_1, u1elo1]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h571, h677, hc15, hlam, hphi, ht01, ht0b, ht5b, p687_1, u1elo1]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [hc01, hlam, hphi, p687_1, u1elo1]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [hlam, p687_0]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h571, hc01, hlam, hphi, p687_1, u1elo1]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          rcases p687_3 (m.d 0 1) (by simp) with h696 | h696
                          · linarith only [h0, h696, hlam]
                          · linarith only [h675, h696, hlam]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          rcases p687_3 (m.d 0 1) (by simp) with h699 | h699
                          · linarith only [h0, h699, hlam]
                          · linarith only [h676, h699, hlam]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h676, h678, h684, h685, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p687_1, u1elo2]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h677, hlam, p687_1]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [hlam, p687_0]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          rcases p687_3 (m.d 0 1) (by simp) with h705 | h705
                          · linarith only [h571, h705, hlam]
                          · linarith only [h675, h705, hlam]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          rcases p687_3 (m.d 0 1) (by simp) with h708 | h708
                          · linarith only [h571, h708, hlam]
                          · linarith only [h676, h708, hlam]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h675, hlam, p687_0]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h677, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p687_1, u1elo3]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h679, hlam, p687_0]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [hlam, p687_0]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h681, hlam, p687_1]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h676, hlam, p687_0]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h678, hlam, p687_1]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h680, hlam, p687_0]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [h676, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p687_1, u1elo0]
                        · have p687_0 := h687c.1
                          have p687_1 := h687c.2.1
                          have p687_2 := h687c.2.2.1
                          have p687_3 := h687c.2.2.2
                          linarith only [hlam, p687_0]
                    · linarith only [h571, h676, h677, h680, h684, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · linarith only [h571, h675, h677, h679, h683, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · linarith only [h571, h680, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h571, h675, h679, hlam]
          · linarith only [h571, h675, h677, h678, hc14, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h726 | h726
          · rcases m.htr 1 3 4 (by decide) (by decide) with h727 | h727
            · rcases m.htr 1 3 5 (by decide) (by decide) with h728 | h728
              · rcases m.htr 1 4 5 (by decide) (by decide) with h729 | h729
                · linarith only [h0, h675, h677, h729, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h731 | h731
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h732 | h732
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h733 | h733
                      · linarith only [h727, h729, h733, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases h1bigk with h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [hlam, p735_0]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h0, hlam, p735_0]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h571, hlam, p735_0]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h0, h677, h727, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo2]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h0, h677, hc15, hlam, hphi, ht01, ht0b, ht5b, p735_1, u1elo2]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h677, hc01, hlam, hphi, p735_1, u1elo2]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [hlam, p735_0]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h677, hlam, p735_0]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          rcases p735_3 (m.d 0 1) (by simp) with h744 | h744
                          · linarith only [h0, h744, hlam]
                          · linarith only [h675, h744, hlam]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          rcases p735_3 (m.d 0 1) (by simp) with h747 | h747
                          · linarith only [h0, h747, hlam]
                          · linarith only [h676, h747, hlam]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h676, h726, h732, h733, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo2]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h0, h676, h726, h732, h733, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo2]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [hlam, p735_0]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          rcases p735_3 (m.d 0 1) (by simp) with h753 | h753
                          · linarith only [h571, h753, hlam]
                          · linarith only [h675, h753, hlam]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          rcases p735_3 (m.d 0 1) (by simp) with h756 | h756
                          · linarith only [h571, h756, hlam]
                          · linarith only [h676, h756, hlam]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h675, hlam, p735_0]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h0, h676, h726, h732, h733, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo3]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h727, hlam, p735_0]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [hlam, p735_0]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h729, hlam, p735_1]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h676, hlam, p735_0]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h726, hlam, p735_1]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h728, hlam, p735_0]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [h0, h676, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p735_1, u1elo1]
                        · have p735_0 := h735c.1
                          have p735_1 := h735c.2.1
                          have p735_2 := h735c.2.2.1
                          have p735_3 := h735c.2.2.2
                          linarith only [hlam, p735_0]
                    · linarith only [h0, h677, h732, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h676, h677, h727, h729, h731, hlam]
              · linarith only [h571, h728, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h675, h677, h727, hlam]
          · linarith only [h0, h675, h726, hc14, hlam, hphi, ht45, u5elo2]
      · linarith only [h675, h676, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h775 | h775
      · rcases m.htr 1 2 3 (by decide) (by decide) with h776 | h776
        · rcases m.htr 1 2 5 (by decide) (by decide) with h777 | h777
          · rcases m.htr 1 3 4 (by decide) (by decide) with h778 | h778
            · rcases m.htr 1 3 5 (by decide) (by decide) with h779 | h779
              · rcases m.htr 1 4 5 (by decide) (by decide) with h780 | h780
                · rcases m.htr 2 3 4 (by decide) (by decide) with h781 | h781
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h782 | h782
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h783 | h783
                      · linarith only [h776, h781, h783, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h675, h775, h778, h780, h783, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · linarith only [h675, h775, h776, h778, h779, h782, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h787 | h787
                    · linarith only [h776, h778, h781, h787, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h675, h775, h776, h778, h779, h787, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h675, h780, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h675, h778, h779, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h792 | h792
              · rcases m.htr 1 4 5 (by decide) (by decide) with h793 | h793
                · rcases m.htr 2 3 4 (by decide) (by decide) with h794 | h794
                  · linarith only [h571, h775, h777, h778, h794, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h796 | h796
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h797 | h797
                      · rcases h1bigk with h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h0, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h571, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h675, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h571, h776, h777, h796, h797, hc45, hlam, hphi, ht01, ht0b, ht5b, p798_1, u1elo1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [hc01, hlam, hphi, p798_1, u1elo1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h571, h775, h777, h796, h797, hc45, hlam, hphi, ht01, ht0b, ht5b, p798_1, u1elo1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h571, h775, h777, h778, h796, h797, hc45, hlam, hphi, ht01, ht0b, ht5b, p798_1, u1elo1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          rcases p798_3 (m.d 0 1) (by simp) with h808 | h808
                          · linarith only [h0, h808, hlam]
                          · linarith only [h775, h808, hlam]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h775, h777, h796, h797, hc45, hlam, hphi, ht01, ht0b, ht5b, p798_1, u1elo2]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h776, hlam, p798_1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h778, hlam, p798_1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          rcases p798_3 (m.d 0 1) (by simp) with h815 | h815
                          · linarith only [h571, h815, hlam]
                          · linarith only [h775, h815, hlam]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h775, h777, h796, h797, hc45, hlam, hphi, ht01, ht0b, ht5b, p798_1, u1elo3]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h776, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p798_1, u1elo3]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h571, h775, h777, h796, h797, hc45, hlam, hphi, ht01, ht0b, ht5b, p798_1, u1elo3]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          rcases p798_3 (m.d 0 1) (by simp) with h822 | h822
                          · linarith only [h675, h822, hlam]
                          · linarith only [h775, h822, hlam]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h775, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h777, hlam, p798_1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h792, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h793, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [hlam, p798_0]
                      · linarith only [h571, h775, h777, h778, h796, h797, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                    · linarith only [h778, h792, h796, hc23, hc34, hlam, hphi]
                · linarith only [h675, h793, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h571, h792, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h571, h775, h776, h777, hc15, hlam, hphi, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h835 | h835
          · rcases m.htr 1 3 4 (by decide) (by decide) with h836 | h836
            · rcases m.htr 1 3 5 (by decide) (by decide) with h837 | h837
              · rcases m.htr 1 4 5 (by decide) (by decide) with h838 | h838
                · rcases m.htr 2 3 4 (by decide) (by decide) with h839 | h839
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h840 | h840
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h841 | h841
                      · rcases h1bigk with h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h0, hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h571, hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h675, hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h0, h776, h835, h840, h841, hc45, hlam, hphi, ht01, ht0b, ht5b, p842_1, u1elo2]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h776, hc01, hlam, hphi, p842_1, u1elo2]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h776, hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h675, h775, h776, h835, h840, h841, hc45, hlam, hphi, ht01, ht0b, ht5b, p842_1, u1elo2]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          rcases p842_3 (m.d 0 1) (by simp) with h852 | h852
                          · linarith only [h0, h852, hlam]
                          · linarith only [h775, h852, hlam]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h775, h835, h840, h841, hc45, hlam, hphi, ht01, ht0b, ht5b, p842_1, u1elo2]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h0, h775, h835, h840, h841, hc45, hlam, hphi, ht01, ht0b, ht5b, p842_1, u1elo2]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h675, h775, h835, h840, h841, hc45, hlam, hphi, ht01, ht0b, ht5b, p842_1, u1elo2]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          rcases p842_3 (m.d 0 1) (by simp) with h859 | h859
                          · linarith only [h571, h859, hlam]
                          · linarith only [h775, h859, hlam]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h775, h835, h840, h841, hc45, hlam, hphi, ht01, ht0b, ht5b, p842_1, u1elo3]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h0, h775, h835, h836, h840, h841, hc45, hlam, hphi, ht01, ht0b, ht5b, p842_1, u1elo2]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h836, hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          rcases p842_3 (m.d 0 1) (by simp) with h866 | h866
                          · linarith only [h675, h866, hlam]
                          · linarith only [h775, h866, hlam]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h775, hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h835, hlam, p842_1]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h837, hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [h838, hlam, p842_0]
                        · have p842_0 := h842c.1
                          have p842_1 := h842c.2.1
                          have p842_2 := h842c.2.2.1
                          have p842_3 := h842c.2.2.2
                          linarith only [hlam, p842_0]
                      · linarith only [h0, h775, h776, h838, h841, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h776, h840, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h776, h839, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h675, h775, h835, h838, hc25, hlam, hphi, u5elo4]
              · linarith only [h836, h837, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h879 | h879
              · rcases m.htr 1 4 5 (by decide) (by decide) with h880 | h880
                · rcases m.htr 2 3 4 (by decide) (by decide) with h881 | h881
                  · linarith only [h0, h775, h776, h835, h836, h881, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h775, h776, h835, h881, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h0, h775, h776, h835, h836, h880, hc25, hlam, hphi, u5elo4]
              · linarith only [h0, h775, h776, h835, h879, hc25, hlam, hphi, u5elo3]
          · linarith only [h0, h835, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h887 | h887
        · rcases m.htr 1 2 5 (by decide) (by decide) with h888 | h888
          · rcases m.htr 1 3 4 (by decide) (by decide) with h889 | h889
            · rcases m.htr 1 3 5 (by decide) (by decide) with h890 | h890
              · rcases m.htr 1 4 5 (by decide) (by decide) with h891 | h891
                · rcases m.htr 2 3 4 (by decide) (by decide) with h892 | h892
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h893 | h893
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h894 | h894
                      · linarith only [h887, h892, h894, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases h1bigk with h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h0, hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h571, hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h675, hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h775, hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hc01, hlam, hphi, p896_1, u1elo1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h889, h891, h894, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p896_1, u1elo1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h891, h894, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p896_1, u1elo1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h775, hc01, hlam, hphi, p896_1, u1elo1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hc01, hlam, hphi, p896_1, u1elo2]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h887, hlam, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h887, h891, h894, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p896_1, u1elo1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h775, h887, hc01, hlam, hphi, p896_1, u1elo1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hc01, hlam, hphi, p896_1, u1elo3]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h887, h889, hlam, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h889, hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h775, h887, h889, hc01, hlam, hphi, p896_1, u1elo1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hc01, hlam, hphi, p896_1, u1elo4]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h888, hlam, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h890, hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h891, hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hlam, p896_0]
                    · linarith only [h887, h890, h892, h893, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h923 | h923
                    · linarith only [h887, h889, h892, h923, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h925 | h925
                      · rcases h1bigk with h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [hlam, p926_0]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h0, hlam, p926_0]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h571, hlam, p926_0]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h675, hlam, p926_0]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h775, hlam, p926_0]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [hc01, hlam, hphi, p926_1, u1elo1]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [hlam, p926_0]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h889, h923, h925, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p926_1, u1elo1]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h675, hc01, hlam, hphi, p926_1, u1elo1]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h775, hc01, hlam, hphi, p926_1, u1elo1]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [hc01, hlam, hphi, p926_1, u1elo2]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h887, hlam, p926_1]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [hlam, p926_0]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h675, h887, hc01, hlam, hphi, p926_1, u1elo1]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h775, h887, hc01, hlam, hphi, p926_1, u1elo1]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [hc01, hlam, hphi, p926_1, u1elo3]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h887, h889, hlam, p926_1]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h889, hlam, p926_0]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [hlam, p926_0]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h775, h887, h889, hc01, hlam, hphi, p926_1, u1elo1]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [hc01, hlam, hphi, p926_1, u1elo4]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h888, hlam, p926_1]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h890, hlam, p926_0]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [h891, hlam, p926_0]
                        · have p926_0 := h926c.1
                          have p926_1 := h926c.2.1
                          have p926_2 := h926c.2.2.1
                          have p926_3 := h926c.2.2.2
                          linarith only [hlam, p926_0]
                      · linarith only [h887, h889, h891, h892, h925, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h675, h891, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h571, h890, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h955 | h955
              · rcases m.htr 1 4 5 (by decide) (by decide) with h956 | h956
                · rcases m.htr 2 3 4 (by decide) (by decide) with h957 | h957
                  · linarith only [h775, h889, h955, h957, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h959 | h959
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h960 | h960
                      · rcases h1bigk with h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h0, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h571, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h675, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h775, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hc01, hlam, hphi, p961_1, u1elo1]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h775, h955, hc01, hlam, hphi, p961_1, u1elo1]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h775, h889, h955, hc01, hlam, hphi, p961_1, u1elo1]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h775, hc01, hlam, hphi, p961_1, u1elo1]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hc01, hlam, hphi, p961_1, u1elo2]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h887, hlam, p961_1]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h889, hlam, p961_1]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h775, h889, hc01, hc34, hlam, hphi, ht12, ht23, p961_1]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hc01, hlam, hphi, p961_1, u1elo3]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h887, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p961_1, u1elo3]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h571, hc01, hlam, hphi, p961_1, u1elo3]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h775, hc01, hlam, hphi, p961_1, u1elo3]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h955, hc01, hlam, hphi, p961_1, u1elo2]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h888, hlam, p961_1]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h955, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h956, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hlam, p961_0]
                      · linarith only [h889, h960, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h889, h955, h959, hc23, hc34, hlam, hphi]
                · linarith only [h675, h956, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h571, h955, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h571, h887, h888, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h992 | h992
          · rcases m.htr 1 3 4 (by decide) (by decide) with h993 | h993
            · rcases m.htr 1 3 5 (by decide) (by decide) with h994 | h994
              · rcases m.htr 1 4 5 (by decide) (by decide) with h995 | h995
                · rcases m.htr 2 3 4 (by decide) (by decide) with h996 | h996
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h997 | h997
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h998 | h998
                      · rcases h1bigk with h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h0, hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h571, hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h675, hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h775, hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [hc01, hlam, hphi, p999_1, u1elo1]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h887, hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h775, h887, h995, hc01, hlam, hphi, p999_1, u1elo2]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h775, h887, hc01, hlam, hphi, p999_1, u1elo2]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [hc01, hlam, hphi, p999_1, u1elo2]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h992, hc25, hlam, hphi, ht01, ht0b, ht5b, p999_1, u1elo2]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h775, h995, hc01, hlam, hphi, p999_1, u1elo2]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h775, hc01, hlam, hphi, p999_1, u1elo2]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [hc01, hlam, hphi, p999_1, u1elo3]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h775, h992, h993, hc01, hlam, hphi, p999_1, u1elo2]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h993, hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h775, h993, hc01, hlam, hphi, p999_1, u1elo2]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h992, hc01, hlam, hphi, p999_1, u1elo1]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h992, hlam, p999_1]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h994, hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [h995, hlam, p999_0]
                        · have p999_0 := h999c.1
                          have p999_1 := h999c.2.1
                          have p999_2 := h999c.2.2.1
                          have p999_3 := h999c.2.2.2
                          linarith only [hlam, p999_0]
                      · rcases h1bigk with h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h0, hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h571, hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h675, hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h775, hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h887, hc01, hc23, hlam, hphi, ht12, p1025_1]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h887, hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h887, h995, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1025_1]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h775, h887, hc01, hc23, hlam, hphi, ht12, p1025_1]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [hc01, hlam, hphi, p1025_1, u1elo2]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, p1025_1, u1elo2]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h675, hc01, hlam, hphi, p1025_1, u1elo2]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h775, hc01, hlam, hphi, p1025_1, u1elo2]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [hc01, hlam, hphi, p1025_1, u1elo3]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h775, h992, h993, hc01, hlam, hphi, p1025_1, u1elo2]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h993, hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h775, h993, hc01, hlam, hphi, p1025_1, u1elo2]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h992, hc01, hlam, hphi, p1025_1, u1elo1]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h992, hlam, p1025_1]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h994, hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [h995, hlam, p1025_0]
                        · have p1025_0 := h1025c.1
                          have p1025_1 := h1025c.2.1
                          have p1025_2 := h1025c.2.2.1
                          have p1025_3 := h1025c.2.2.2
                          linarith only [hlam, p1025_0]
                    · linarith only [h0, h887, h997, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h775, h887, h992, h996, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h675, h995, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h993, h994, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1055 | h1055
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1056 | h1056
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1057 | h1057
                  · linarith only [h1057, h775, h887, h992, h993, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1057, h775, h887, h992, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h1056, h775, h887, h992, h993, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h1055, h775, h887, h992, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h0, h992, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem r1l7_21_15_M_LI_L_0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h1bigk := hb1.2.2.2
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_15_M_LI_L_0_x0 m hb1 hb5 h0
  · exact r1l7_21_15_M_LI_L_0_x1 m hb1 hb5 h0

end R2N4
