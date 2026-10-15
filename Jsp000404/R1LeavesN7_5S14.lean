import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7120 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7121 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h7122 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h7124 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h7126 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 2 3 4 (by decide) (by decide) with h7530 | h7530
  · linarith only [h6310, h6316, h7118, h7119, h7126, h7530, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h7532 | h7532
    · linarith only [h0, h6311, h6900, h7118, h7119, h7122, h7126, h7532, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h7534 | h7534
      · linarith only [h7120, h7126, h7534, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h7536 | h7536
        · rcases h0bigk with h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [hlam, p7537_0]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h0, hlam, p7537_1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            rcases p7537_3 (m.d 0 1) (by simp) with h7540 | h7540
            · rcases p7537_3 (m.d 0 2) (by simp) with h7541 | h7541
              · rcases p7537_3 (m.d 0 3) (by simp) with h7542 | h7542
                · linarith only [h6310, h7542, hlam]
                · rcases p7537_3 (m.d 0 4) (by simp) with h7544 | h7544
                  · linarith only [h6311, h7544, hlam]
                  · linarith only [h6316, h7544, hlam]
              · linarith only [h6313, h7541, hlam]
            · linarith only [h6310, h7540, hlam]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h0, h7118, h7122, h7126, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7537_1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h0, h7118, h7119, h7122, h7126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7537_1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h6310, h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7537_1, u0elo1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [hlam, p7537_0]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            rcases p7537_3 (m.d 0 1) (by simp) with h7553 | h7553
            · linarith only [h0, h7553, hlam]
            · linarith only [h6310, h7553, hlam]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h7118, h7119, h7122, h7126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7537_1, u0elo1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h7118, h7119, h7122, h7126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7537_1, u0elo1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h6310, hlam, p7537_1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h6313, hlam, p7537_1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [hlam, p7537_0]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h6316, hlam, p7537_1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h6900, hlam, p7537_1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h6311, hlam, p7537_0]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h6314, hlam, p7537_0]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            rcases p7537_3 (m.d 0 1) (by simp) with h7565 | h7565
            · rcases p7537_3 (m.d 0 2) (by simp) with h7566 | h7566
              · rcases p7537_3 (m.d 0 3) (by simp) with h7567 | h7567
                · linarith only [h6316, h7567, hlam]
                · rcases p7537_3 (m.d 0 4) (by simp) with h7569 | h7569
                  · rcases p7537_3 (m.d 0 5) (by simp) with h7570 | h7570
                    · linarith only [h7118, h7570, hlam]
                    · linarith only [h6900, h7570, hlam]
                  · linarith only [h6316, h7569, hlam]
              · linarith only [h6313, h7566, hlam]
            · linarith only [h6310, h7565, hlam]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [hlam, p7537_0]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h6311, h7118, h7119, h7122, h7126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7537_1, u0elo0]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h6312, hlam, p7537_0]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h6315, hlam, p7537_1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            rcases p7537_3 (m.d 0 1) (by simp) with h7580 | h7580
            · rcases p7537_3 (m.d 0 2) (by simp) with h7581 | h7581
              · rcases p7537_3 (m.d 0 3) (by simp) with h7582 | h7582
                · linarith only [h6900, h7582, hlam]
                · rcases p7537_3 (m.d 0 4) (by simp) with h7584 | h7584
                  · rcases p7537_3 (m.d 0 5) (by simp) with h7585 | h7585
                    · rcases h0emin with h7586 | h7586 | h7586 | h7586 | h7586
                      · rcases h1bigk with h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c | h7587c
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [hlam, p7587_0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h0, hlam, p7587_0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          rcases p7587_3 (m.d 0 1) (by simp) with h7590 | h7590
                          · rcases p7587_3 (m.d 1 2) (by simp) with h7591 | h7591
                            · rcases p7587_3 (m.d 1 3) (by simp) with h7592 | h7592
                              · linarith only [h7592, hlam, p7587_0]
                              · rcases p7587_3 (m.d 1 4) (by simp) with h7594 | h7594
                                · linarith only [h6311, h7594, hlam]
                                · linarith only [h7122, h7594, hlam]
                            · linarith only [h7119, h7591, hlam]
                          · linarith only [h7590, hlam, p7587_0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          rcases p7587_3 (m.d 0 1) (by simp) with h7599 | h7599
                          · rcases p7587_3 (m.d 1 2) (by simp) with h7600 | h7600
                            · rcases p7587_3 (m.d 1 3) (by simp) with h7601 | h7601
                              · linarith only [h6310, h7601, hlam]
                              · rcases p7587_3 (m.d 1 4) (by simp) with h7603 | h7603
                                · linarith only [h7603, hlam, p7587_0]
                                · rcases p7587_3 (m.d 1 5) (by simp) with h7605 | h7605
                                  · linarith only [h6312, h7605, hlam]
                                  · linarith only [h7126, h7605, hlam]
                            · linarith only [h7120, h7600, hlam]
                          · linarith only [h7599, hlam, p7587_0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          rcases p7587_3 (m.d 0 1) (by simp) with h7610 | h7610
                          · rcases p7587_3 (m.d 1 2) (by simp) with h7611 | h7611
                            · rcases p7587_3 (m.d 1 3) (by simp) with h7612 | h7612
                              · linarith only [h6310, h7612, hlam]
                              · rcases p7587_3 (m.d 1 4) (by simp) with h7614 | h7614
                                · linarith only [h6311, h7614, hlam]
                                · rcases p7587_3 (m.d 1 5) (by simp) with h7616 | h7616
                                  · linarith only [h7616, hlam, p7587_0]
                                  · rcases h3bigk with h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c | h7618c
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7537_1, p7618_1, u0elo4]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h0, h6312, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7537_1, p7618_1]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h6316, hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h6900, hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h6310, hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h7122, h7126, hc23, hc45, hlam, hphi, ht34, p7618_1]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h7122, hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h7124, hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h6313, hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h7119, hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h7530, hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h7532, hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      rcases p7618_3 (m.d 0 3) (by simp) with h7634 | h7634
                                      · linarith only [h7634, hlam, p7618_0]
                                      · rcases p7618_3 (m.d 1 3) (by simp) with h7636 | h7636
                                        · linarith only [h7122, h7636, hlam]
                                        · rcases p7618_3 (m.d 2 3) (by simp) with h7638 | h7638
                                          · linarith only [h7530, h7638, hlam]
                                          · rcases p7618_3 (m.d 3 4) (by simp) with h7640 | h7640
                                            · rcases p7618_3 (m.d 3 5) (by simp) with h7641 | h7641
                                              · linarith only [h7536, h7641, hlam]
                                              · linarith only [h6900, h7641, hlam]
                                            · linarith only [h7640, hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      rcases p7618_3 (m.d 0 3) (by simp) with h7645 | h7645
                                      · linarith only [h6316, h7645, hlam]
                                      · linarith only [h6310, h7645, hlam]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      rcases p7618_3 (m.d 0 3) (by simp) with h7648 | h7648
                                      · linarith only [h6316, h7648, hlam]
                                      · linarith only [h6313, h7648, hlam]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h6900, hc03, hc34, hlam, hphi, p7537_1, p7618_1]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      rcases p7618_3 (m.d 0 3) (by simp) with h7653 | h7653
                                      · linarith only [h7653, hlam, p7618_0]
                                      · rcases p7618_3 (m.d 1 3) (by simp) with h7655 | h7655
                                        · linarith only [h7124, h7655, hlam]
                                        · rcases p7618_3 (m.d 2 3) (by simp) with h7657 | h7657
                                          · linarith only [h7532, h7657, hlam]
                                          · rcases p7618_3 (m.d 3 4) (by simp) with h7659 | h7659
                                            · rcases p7618_3 (m.d 3 5) (by simp) with h7660 | h7660
                                              · rcases h4bigk with h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c | h7661c
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [hlam, p7661_0]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  rcases p7661_3 (m.d 0 4) (by simp) with h7663 | h7663
                                                  · rcases p7661_3 (m.d 1 4) (by simp) with h7664 | h7664
                                                    · linarith only [h6311, h7664, hlam]
                                                    · rcases p7661_3 (m.d 2 4) (by simp) with h7666 | h7666
                                                      · linarith only [h6314, h7666, hlam]
                                                      · rcases p7661_3 (m.d 3 4) (by simp) with h7668 | h7668
                                                        · rcases p7661_3 (m.d 4 5) (by simp) with h7669 | h7669
                                                          · linarith only [h7118, h7669, hlam]
                                                          · linarith only [h7126, h7669, hlam]
                                                        · linarith only [h7122, h7668, hlam]
                                                  · linarith only [h6311, h7663, hlam]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  rcases p7661_3 (m.d 0 4) (by simp) with h7674 | h7674
                                                  · rcases p7661_3 (m.d 1 4) (by simp) with h7675 | h7675
                                                    · linarith only [h6311, h7675, hlam]
                                                    · linarith only [h7120, h7675, hlam]
                                                  · linarith only [h6314, h7674, hlam]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h6316, hlam, p7661_0]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h0, h6311, h7126, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7661_1]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h6311, hlam, p7661_1]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [hlam, p7661_0]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h7126, h7530, hc23, hc45, hlam, hphi, ht34, p7661_1]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h7122, hlam, p7661_1]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h7126, hlam, p7661_0]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h6314, hlam, p7661_1]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h7120, hlam, p7661_1]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [hlam, p7661_0]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h7530, hlam, p7661_1]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h7534, hlam, p7661_0]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h6310, h7118, h7119, hc23, hc34, hlam, hphi, p7537_1, p7661_1]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  rcases p7661_3 (m.d 0 4) (by simp) with h7692 | h7692
                                                  · linarith only [h6316, h7692, hlam]
                                                  · linarith only [h6311, h7692, hlam]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  rcases p7661_3 (m.d 0 4) (by simp) with h7695 | h7695
                                                  · linarith only [h6316, h7695, hlam]
                                                  · linarith only [h6314, h7695, hlam]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [hlam, p7661_0]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h7120, h7126, h7530, hc23, hc34, hlam, hphi, p7661_1]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h7118, hlam, p7661_0]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h0, h6311, h7118, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7661_1]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h0, h6311, h7118, h7530, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7661_1]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [h7536, hlam, p7661_0]
                                                · have p7661_0 := h7661c.1
                                                  have p7661_1 := h7661c.2.1
                                                  have p7661_2 := h7661c.2.2.1
                                                  have p7661_3 := h7661c.2.2.2
                                                  linarith only [hlam, p7661_0]
                                              · linarith only [h7660, hlam, p7618_0]
                                            · linarith only [h6316, h7659, hlam]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      rcases p7618_3 (m.d 0 3) (by simp) with h7707 | h7707
                                      · linarith only [h6900, h7707, hlam]
                                      · linarith only [h6310, h7707, hlam]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      rcases p7618_3 (m.d 0 3) (by simp) with h7710 | h7710
                                      · linarith only [h6900, h7710, hlam]
                                      · linarith only [h6313, h7710, hlam]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [h7536, hlam, p7618_0]
                                    · have p7618_0 := h7618c.1
                                      have p7618_1 := h7618c.2.1
                                      have p7618_2 := h7618c.2.2.1
                                      have p7618_3 := h7618c.2.2.2
                                      linarith only [hlam, p7618_0]
                            · linarith only [h7121, h7611, hlam]
                          · linarith only [h7610, hlam, p7587_0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h7586, hc12, hlam, ht01, p7587_1]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [hlam, p7587_0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h0, h6310, h6311, h7118, hlam, p7537_1, p7587_2]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h0, h6311, h7118, h7126, hlam, p7587_2]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          rcases p7587_3 (m.d 0 1) (by simp) with h7721 | h7721
                          · linarith only [h0, h7721, hlam]
                          · linarith only [h6312, h7721, hlam]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h6310, hlam, p7587_0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h7119, hlam, p7587_1]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [hlam, p7587_0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h7122, hlam, p7587_1]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h7124, hlam, p7587_1]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h6311, hlam, p7587_0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h7120, hlam, p7587_1]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h6311, h7118, h7119, h7126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7587_1, u0elo0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [hlam, p7587_0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h7126, hlam, p7587_1]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h6312, hlam, p7587_0]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h7121, hlam, p7587_1]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h0, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7587_1]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [h0, h6311, h7118, h7126, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7587_1]
                        · have p7587_0 := h7587c.1
                          have p7587_1 := h7587c.2.1
                          have p7587_2 := h7587c.2.2.1
                          have p7587_3 := h7587c.2.2.2
                          linarith only [hlam, p7587_0]
                      · rcases h1bigk with h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c | h7739c
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [hlam, p7739_0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h0, hlam, p7739_0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          rcases p7739_3 (m.d 0 1) (by simp) with h7742 | h7742
                          · rcases p7739_3 (m.d 1 2) (by simp) with h7743 | h7743
                            · rcases p7739_3 (m.d 1 3) (by simp) with h7744 | h7744
                              · linarith only [h7744, hlam, p7739_0]
                              · rcases p7739_3 (m.d 1 4) (by simp) with h7746 | h7746
                                · linarith only [h6311, h7746, hlam]
                                · linarith only [h7122, h7746, hlam]
                            · linarith only [h7119, h7743, hlam]
                          · linarith only [h7742, hlam, p7739_0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          rcases p7739_3 (m.d 0 1) (by simp) with h7751 | h7751
                          · rcases p7739_3 (m.d 1 2) (by simp) with h7752 | h7752
                            · rcases p7739_3 (m.d 1 3) (by simp) with h7753 | h7753
                              · linarith only [h6310, h7753, hlam]
                              · rcases p7739_3 (m.d 1 4) (by simp) with h7755 | h7755
                                · linarith only [h7755, hlam, p7739_0]
                                · rcases p7739_3 (m.d 1 5) (by simp) with h7757 | h7757
                                  · linarith only [h6312, h7757, hlam]
                                  · linarith only [h7126, h7757, hlam]
                            · linarith only [h7120, h7752, hlam]
                          · linarith only [h7751, hlam, p7739_0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          rcases p7739_3 (m.d 0 1) (by simp) with h7762 | h7762
                          · rcases p7739_3 (m.d 1 2) (by simp) with h7763 | h7763
                            · rcases p7739_3 (m.d 1 3) (by simp) with h7764 | h7764
                              · linarith only [h6310, h7764, hlam]
                              · rcases p7739_3 (m.d 1 4) (by simp) with h7766 | h7766
                                · linarith only [h6311, h7766, hlam]
                                · rcases p7739_3 (m.d 1 5) (by simp) with h7768 | h7768
                                  · linarith only [h7768, hlam, p7739_0]
                                  · rcases h3bigk with h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7537_1, p7770_1, u0elo4]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h0, h6312, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7537_1, p7770_1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h6316, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h6900, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h6310, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h0, h6310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7770_1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7122, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7124, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h6313, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7119, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7530, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7532, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      rcases p7770_3 (m.d 0 3) (by simp) with h7786 | h7786
                                      · linarith only [h7786, hlam, p7770_0]
                                      · rcases p7770_3 (m.d 1 3) (by simp) with h7788 | h7788
                                        · linarith only [h7122, h7788, hlam]
                                        · rcases p7770_3 (m.d 2 3) (by simp) with h7790 | h7790
                                          · linarith only [h7530, h7790, hlam]
                                          · rcases p7770_3 (m.d 3 4) (by simp) with h7792 | h7792
                                            · rcases p7770_3 (m.d 3 5) (by simp) with h7793 | h7793
                                              · linarith only [h7536, h7793, hlam]
                                              · linarith only [h6900, h7793, hlam]
                                            · linarith only [h7792, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      rcases p7770_3 (m.d 0 3) (by simp) with h7797 | h7797
                                      · linarith only [h6316, h7797, hlam]
                                      · linarith only [h6310, h7797, hlam]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      rcases p7770_3 (m.d 0 3) (by simp) with h7800 | h7800
                                      · linarith only [h6316, h7800, hlam]
                                      · linarith only [h6313, h7800, hlam]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h6900, hc03, hc34, hlam, hphi, p7537_1, p7770_1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      rcases p7770_3 (m.d 0 3) (by simp) with h7805 | h7805
                                      · linarith only [h7805, hlam, p7770_0]
                                      · rcases p7770_3 (m.d 1 3) (by simp) with h7807 | h7807
                                        · linarith only [h7124, h7807, hlam]
                                        · rcases p7770_3 (m.d 2 3) (by simp) with h7809 | h7809
                                          · linarith only [h7532, h7809, hlam]
                                          · rcases p7770_3 (m.d 3 4) (by simp) with h7811 | h7811
                                            · rcases p7770_3 (m.d 3 5) (by simp) with h7812 | h7812
                                              · rcases h4bigk with h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c | h7813c
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [hlam, p7813_0]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  rcases p7813_3 (m.d 0 4) (by simp) with h7815 | h7815
                                                  · rcases p7813_3 (m.d 1 4) (by simp) with h7816 | h7816
                                                    · linarith only [h6311, h7816, hlam]
                                                    · rcases p7813_3 (m.d 2 4) (by simp) with h7818 | h7818
                                                      · linarith only [h6314, h7818, hlam]
                                                      · rcases p7813_3 (m.d 3 4) (by simp) with h7820 | h7820
                                                        · rcases p7813_3 (m.d 4 5) (by simp) with h7821 | h7821
                                                          · linarith only [h7118, h7821, hlam]
                                                          · linarith only [h7126, h7821, hlam]
                                                        · linarith only [h7122, h7820, hlam]
                                                  · linarith only [h6311, h7815, hlam]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  rcases p7813_3 (m.d 0 4) (by simp) with h7826 | h7826
                                                  · rcases p7813_3 (m.d 1 4) (by simp) with h7827 | h7827
                                                    · linarith only [h6311, h7827, hlam]
                                                    · linarith only [h7120, h7827, hlam]
                                                  · linarith only [h6314, h7826, hlam]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h6316, hlam, p7813_0]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h0, h6311, h7119, h7122, h7126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7813_1]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h6311, hlam, p7813_1]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [hlam, p7813_0]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h7126, h7530, hc23, hc45, hlam, hphi, ht34, p7813_1]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h7122, hlam, p7813_1]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h7126, hlam, p7813_0]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h6314, hlam, p7813_1]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h7120, hlam, p7813_1]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [hlam, p7813_0]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h7530, hlam, p7813_1]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h7534, hlam, p7813_0]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h7118, hc03, hc34, hlam, hphi, p7537_1, p7813_1]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  rcases p7813_3 (m.d 0 4) (by simp) with h7844 | h7844
                                                  · linarith only [h6316, h7844, hlam]
                                                  · linarith only [h6311, h7844, hlam]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  rcases p7813_3 (m.d 0 4) (by simp) with h7847 | h7847
                                                  · linarith only [h6316, h7847, hlam]
                                                  · linarith only [h6314, h7847, hlam]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [hlam, p7813_0]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h7120, h7126, h7530, hc23, hc34, hlam, hphi, p7813_1]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h7118, hlam, p7813_0]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h7118, hc14, hlam, hphi, ht0b, ht45, ht5b, p7813_1, u0elo3]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h0, h6311, h7118, h7530, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7813_1]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [h7536, hlam, p7813_0]
                                                · have p7813_0 := h7813c.1
                                                  have p7813_1 := h7813c.2.1
                                                  have p7813_2 := h7813c.2.2.1
                                                  have p7813_3 := h7813c.2.2.2
                                                  linarith only [hlam, p7813_0]
                                              · linarith only [h7812, hlam, p7770_0]
                                            · linarith only [h6316, h7811, hlam]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      rcases p7770_3 (m.d 0 3) (by simp) with h7859 | h7859
                                      · linarith only [h6900, h7859, hlam]
                                      · linarith only [h6310, h7859, hlam]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      rcases p7770_3 (m.d 0 3) (by simp) with h7862 | h7862
                                      · linarith only [h6900, h7862, hlam]
                                      · linarith only [h6313, h7862, hlam]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7536, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [hlam, p7770_0]
                            · linarith only [h7121, h7763, hlam]
                          · linarith only [h7762, hlam, p7739_0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h6310, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7537_1, p7739_1]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [hlam, p7739_0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h0, h6310, h6311, h7118, hlam, p7537_1, p7739_2]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h0, h6311, h7118, h7126, hlam, p7739_2]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          rcases p7739_3 (m.d 0 1) (by simp) with h7873 | h7873
                          · linarith only [h0, h7873, hlam]
                          · linarith only [h6312, h7873, hlam]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h6310, hlam, p7739_0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h7119, hlam, p7739_1]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [hlam, p7739_0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h7122, hlam, p7739_1]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h7124, hlam, p7739_1]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h6311, hlam, p7739_0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h7120, hlam, p7739_1]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h6311, h7118, h7119, h7126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7739_1, u0elo0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [hlam, p7739_0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h7126, hlam, p7739_1]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h6312, hlam, p7739_0]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h7121, hlam, p7739_1]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h0, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7739_1]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [h0, h6311, h7118, h7126, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7739_1]
                        · have p7739_0 := h7739c.1
                          have p7739_1 := h7739c.2.1
                          have p7739_2 := h7739c.2.2.1
                          have p7739_3 := h7739c.2.2.2
                          linarith only [hlam, p7739_0]
                      · linarith only [h7586, hlam, p7537_1, u0elo4]
                      · rcases h1bigk with h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c | h7892c
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [hlam, p7892_0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h0, hlam, p7892_0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          rcases p7892_3 (m.d 0 1) (by simp) with h7895 | h7895
                          · rcases p7892_3 (m.d 1 2) (by simp) with h7896 | h7896
                            · rcases p7892_3 (m.d 1 3) (by simp) with h7897 | h7897
                              · linarith only [h7897, hlam, p7892_0]
                              · rcases p7892_3 (m.d 1 4) (by simp) with h7899 | h7899
                                · linarith only [h6311, h7899, hlam]
                                · linarith only [h7122, h7899, hlam]
                            · linarith only [h7119, h7896, hlam]
                          · linarith only [h7895, hlam, p7892_0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          rcases p7892_3 (m.d 0 1) (by simp) with h7904 | h7904
                          · rcases p7892_3 (m.d 1 2) (by simp) with h7905 | h7905
                            · rcases p7892_3 (m.d 1 3) (by simp) with h7906 | h7906
                              · linarith only [h6310, h7906, hlam]
                              · rcases p7892_3 (m.d 1 4) (by simp) with h7908 | h7908
                                · linarith only [h7908, hlam, p7892_0]
                                · rcases p7892_3 (m.d 1 5) (by simp) with h7910 | h7910
                                  · linarith only [h6312, h7910, hlam]
                                  · linarith only [h7126, h7910, hlam]
                            · linarith only [h7120, h7905, hlam]
                          · linarith only [h7904, hlam, p7892_0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          rcases p7892_3 (m.d 0 1) (by simp) with h7915 | h7915
                          · rcases p7892_3 (m.d 1 2) (by simp) with h7916 | h7916
                            · rcases p7892_3 (m.d 1 3) (by simp) with h7917 | h7917
                              · linarith only [h6310, h7917, hlam]
                              · rcases p7892_3 (m.d 1 4) (by simp) with h7919 | h7919
                                · linarith only [h6311, h7919, hlam]
                                · rcases p7892_3 (m.d 1 5) (by simp) with h7921 | h7921
                                  · linarith only [h7921, hlam, p7892_0]
                                  · rcases h3bigk with h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c | h7923c
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h0, h6311, h7118, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7537_1, p7923_1]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h0, h6311, h7118, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7537_1, p7923_1]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h6316, hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h6900, hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h6310, hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h0, h6310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7923_1]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h7122, hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h7124, hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h6313, hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h7119, hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h7530, hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h7532, hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      rcases p7923_3 (m.d 0 3) (by simp) with h7939 | h7939
                                      · linarith only [h7939, hlam, p7923_0]
                                      · rcases p7923_3 (m.d 1 3) (by simp) with h7941 | h7941
                                        · linarith only [h7122, h7941, hlam]
                                        · rcases p7923_3 (m.d 2 3) (by simp) with h7943 | h7943
                                          · linarith only [h7530, h7943, hlam]
                                          · rcases p7923_3 (m.d 3 4) (by simp) with h7945 | h7945
                                            · rcases p7923_3 (m.d 3 5) (by simp) with h7946 | h7946
                                              · linarith only [h7536, h7946, hlam]
                                              · linarith only [h6900, h7946, hlam]
                                            · linarith only [h7945, hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      rcases p7923_3 (m.d 0 3) (by simp) with h7950 | h7950
                                      · linarith only [h6316, h7950, hlam]
                                      · linarith only [h6310, h7950, hlam]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      rcases p7923_3 (m.d 0 3) (by simp) with h7953 | h7953
                                      · linarith only [h6316, h7953, hlam]
                                      · linarith only [h6313, h7953, hlam]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h6900, hc03, hc34, hlam, hphi, p7537_1, p7923_1]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      rcases p7923_3 (m.d 0 3) (by simp) with h7958 | h7958
                                      · linarith only [h7958, hlam, p7923_0]
                                      · rcases p7923_3 (m.d 1 3) (by simp) with h7960 | h7960
                                        · linarith only [h7124, h7960, hlam]
                                        · rcases p7923_3 (m.d 2 3) (by simp) with h7962 | h7962
                                          · linarith only [h7532, h7962, hlam]
                                          · rcases p7923_3 (m.d 3 4) (by simp) with h7964 | h7964
                                            · rcases p7923_3 (m.d 3 5) (by simp) with h7965 | h7965
                                              · rcases h4bigk with h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [hlam, p7966_0]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  rcases p7966_3 (m.d 0 4) (by simp) with h7968 | h7968
                                                  · rcases p7966_3 (m.d 1 4) (by simp) with h7969 | h7969
                                                    · linarith only [h6311, h7969, hlam]
                                                    · rcases p7966_3 (m.d 2 4) (by simp) with h7971 | h7971
                                                      · linarith only [h6314, h7971, hlam]
                                                      · rcases p7966_3 (m.d 3 4) (by simp) with h7973 | h7973
                                                        · rcases p7966_3 (m.d 4 5) (by simp) with h7974 | h7974
                                                          · linarith only [h7118, h7974, hlam]
                                                          · linarith only [h7126, h7974, hlam]
                                                        · linarith only [h7122, h7973, hlam]
                                                  · linarith only [h6311, h7968, hlam]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  rcases p7966_3 (m.d 0 4) (by simp) with h7979 | h7979
                                                  · rcases p7966_3 (m.d 1 4) (by simp) with h7980 | h7980
                                                    · linarith only [h6311, h7980, hlam]
                                                    · linarith only [h7120, h7980, hlam]
                                                  · linarith only [h6314, h7979, hlam]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h6316, hlam, p7966_0]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h0, h6311, h7120, h7126, h7530, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7966_1]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h6311, hlam, p7966_1]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [hlam, p7966_0]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h0, h6311, h7530, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7966_1]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h7122, hlam, p7966_1]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h7126, hlam, p7966_0]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h6314, hlam, p7966_1]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h7120, hlam, p7966_1]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [hlam, p7966_0]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h7530, hlam, p7966_1]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h7534, hlam, p7966_0]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h7586, hc34, hlam, ht01, ht12, ht23, p7966_1]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  rcases p7966_3 (m.d 0 4) (by simp) with h7997 | h7997
                                                  · linarith only [h6316, h7997, hlam]
                                                  · linarith only [h6311, h7997, hlam]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  rcases p7966_3 (m.d 0 4) (by simp) with h8000 | h8000
                                                  · linarith only [h6316, h8000, hlam]
                                                  · linarith only [h6314, h8000, hlam]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [hlam, p7966_0]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h7120, h7126, h7530, hc23, hc34, hlam, hphi, p7966_1]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h7118, hlam, p7966_0]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h0, h6311, h7118, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7966_1]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h0, h6311, h7118, h7530, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7966_1]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [h7536, hlam, p7966_0]
                                                · have p7966_0 := h7966c.1
                                                  have p7966_1 := h7966c.2.1
                                                  have p7966_2 := h7966c.2.2.1
                                                  have p7966_3 := h7966c.2.2.2
                                                  linarith only [hlam, p7966_0]
                                              · linarith only [h7965, hlam, p7923_0]
                                            · linarith only [h6316, h7964, hlam]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      rcases p7923_3 (m.d 0 3) (by simp) with h8012 | h8012
                                      · linarith only [h6900, h8012, hlam]
                                      · linarith only [h6310, h8012, hlam]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      rcases p7923_3 (m.d 0 3) (by simp) with h8015 | h8015
                                      · linarith only [h6900, h8015, hlam]
                                      · linarith only [h6313, h8015, hlam]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [h7536, hlam, p7923_0]
                                    · have p7923_0 := h7923c.1
                                      have p7923_1 := h7923c.2.1
                                      have p7923_2 := h7923c.2.2.1
                                      have p7923_3 := h7923c.2.2.2
                                      linarith only [hlam, p7923_0]
                            · linarith only [h7121, h7916, hlam]
                          · linarith only [h7915, hlam, p7892_0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h6311, h7118, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7537_1, p7892_1]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [hlam, p7892_0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h0, h6310, h6311, h7118, hlam, p7537_1, p7892_2]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h0, h6311, h7118, h7126, hlam, p7892_2]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          rcases p7892_3 (m.d 0 1) (by simp) with h8026 | h8026
                          · linarith only [h0, h8026, hlam]
                          · linarith only [h6312, h8026, hlam]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h6310, hlam, p7892_0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h7119, hlam, p7892_1]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [hlam, p7892_0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h7122, hlam, p7892_1]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h7124, hlam, p7892_1]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h6311, hlam, p7892_0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h7120, hlam, p7892_1]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h6311, h7118, h7119, h7126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7892_1, u0elo0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [hlam, p7892_0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h7126, hlam, p7892_1]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h6312, hlam, p7892_0]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h7121, hlam, p7892_1]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h0, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7892_1]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [h0, h6311, h7118, h7126, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7892_1]
                        · have p7892_0 := h7892c.1
                          have p7892_1 := h7892c.2.1
                          have p7892_2 := h7892c.2.2.1
                          have p7892_3 := h7892c.2.2.2
                          linarith only [hlam, p7892_0]
                      · rcases h1bigk with h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c | h8044c
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [hlam, p8044_0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h0, hlam, p8044_0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          rcases p8044_3 (m.d 0 1) (by simp) with h8047 | h8047
                          · rcases p8044_3 (m.d 1 2) (by simp) with h8048 | h8048
                            · rcases p8044_3 (m.d 1 3) (by simp) with h8049 | h8049
                              · linarith only [h8049, hlam, p8044_0]
                              · rcases p8044_3 (m.d 1 4) (by simp) with h8051 | h8051
                                · linarith only [h6311, h8051, hlam]
                                · linarith only [h7122, h8051, hlam]
                            · linarith only [h7119, h8048, hlam]
                          · linarith only [h8047, hlam, p8044_0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          rcases p8044_3 (m.d 0 1) (by simp) with h8056 | h8056
                          · rcases p8044_3 (m.d 1 2) (by simp) with h8057 | h8057
                            · rcases p8044_3 (m.d 1 3) (by simp) with h8058 | h8058
                              · linarith only [h6310, h8058, hlam]
                              · rcases p8044_3 (m.d 1 4) (by simp) with h8060 | h8060
                                · linarith only [h8060, hlam, p8044_0]
                                · rcases p8044_3 (m.d 1 5) (by simp) with h8062 | h8062
                                  · linarith only [h6312, h8062, hlam]
                                  · linarith only [h7126, h8062, hlam]
                            · linarith only [h7120, h8057, hlam]
                          · linarith only [h8056, hlam, p8044_0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          rcases p8044_3 (m.d 0 1) (by simp) with h8067 | h8067
                          · rcases p8044_3 (m.d 1 2) (by simp) with h8068 | h8068
                            · rcases p8044_3 (m.d 1 3) (by simp) with h8069 | h8069
                              · linarith only [h6310, h8069, hlam]
                              · rcases p8044_3 (m.d 1 4) (by simp) with h8071 | h8071
                                · linarith only [h6311, h8071, hlam]
                                · rcases p8044_3 (m.d 1 5) (by simp) with h8073 | h8073
                                  · linarith only [h8073, hlam, p8044_0]
                                  · rcases h3bigk with h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c | h8075c
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7537_1, p8075_1, u0elo4]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h0, h6312, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7537_1, p8075_1]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h6316, hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h6900, hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h6310, hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h0, h6310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8075_1]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h7122, hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h7124, hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h6313, hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h7119, hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h7530, hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h7532, hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      rcases p8075_3 (m.d 0 3) (by simp) with h8091 | h8091
                                      · linarith only [h8091, hlam, p8075_0]
                                      · rcases p8075_3 (m.d 1 3) (by simp) with h8093 | h8093
                                        · linarith only [h7122, h8093, hlam]
                                        · rcases p8075_3 (m.d 2 3) (by simp) with h8095 | h8095
                                          · linarith only [h7530, h8095, hlam]
                                          · rcases p8075_3 (m.d 3 4) (by simp) with h8097 | h8097
                                            · rcases p8075_3 (m.d 3 5) (by simp) with h8098 | h8098
                                              · linarith only [h7536, h8098, hlam]
                                              · linarith only [h6900, h8098, hlam]
                                            · linarith only [h8097, hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      rcases p8075_3 (m.d 0 3) (by simp) with h8102 | h8102
                                      · linarith only [h6316, h8102, hlam]
                                      · linarith only [h6310, h8102, hlam]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      rcases p8075_3 (m.d 0 3) (by simp) with h8105 | h8105
                                      · linarith only [h6316, h8105, hlam]
                                      · linarith only [h6313, h8105, hlam]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h6900, hc03, hc34, hlam, hphi, p7537_1, p8075_1]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      rcases p8075_3 (m.d 0 3) (by simp) with h8110 | h8110
                                      · linarith only [h8110, hlam, p8075_0]
                                      · rcases p8075_3 (m.d 1 3) (by simp) with h8112 | h8112
                                        · linarith only [h7124, h8112, hlam]
                                        · rcases p8075_3 (m.d 2 3) (by simp) with h8114 | h8114
                                          · linarith only [h7532, h8114, hlam]
                                          · rcases p8075_3 (m.d 3 4) (by simp) with h8116 | h8116
                                            · rcases p8075_3 (m.d 3 5) (by simp) with h8117 | h8117
                                              · rcases h4bigk with h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c | h8118c
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [hlam, p8118_0]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  rcases p8118_3 (m.d 0 4) (by simp) with h8120 | h8120
                                                  · rcases p8118_3 (m.d 1 4) (by simp) with h8121 | h8121
                                                    · linarith only [h6311, h8121, hlam]
                                                    · rcases p8118_3 (m.d 2 4) (by simp) with h8123 | h8123
                                                      · linarith only [h6314, h8123, hlam]
                                                      · rcases p8118_3 (m.d 3 4) (by simp) with h8125 | h8125
                                                        · rcases p8118_3 (m.d 4 5) (by simp) with h8126 | h8126
                                                          · linarith only [h7118, h8126, hlam]
                                                          · linarith only [h7126, h8126, hlam]
                                                        · linarith only [h7122, h8125, hlam]
                                                  · linarith only [h6311, h8120, hlam]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  rcases p8118_3 (m.d 0 4) (by simp) with h8131 | h8131
                                                  · rcases p8118_3 (m.d 1 4) (by simp) with h8132 | h8132
                                                    · linarith only [h6311, h8132, hlam]
                                                    · linarith only [h7120, h8132, hlam]
                                                  · linarith only [h6314, h8131, hlam]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h6316, hlam, p8118_0]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h0, h6311, h7120, h7126, h7530, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8118_1]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h6311, hlam, p8118_1]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [hlam, p8118_0]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h0, h6311, h7530, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8118_1]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h7122, hlam, p8118_1]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h7126, hlam, p8118_0]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h6314, hlam, p8118_1]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h7120, hlam, p8118_1]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [hlam, p8118_0]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h7530, hlam, p8118_1]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h7534, hlam, p8118_0]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h6310, h7118, h7119, hc23, hc34, hlam, hphi, p7537_1, p8118_1]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  rcases p8118_3 (m.d 0 4) (by simp) with h8149 | h8149
                                                  · linarith only [h6316, h8149, hlam]
                                                  · linarith only [h6311, h8149, hlam]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  rcases p8118_3 (m.d 0 4) (by simp) with h8152 | h8152
                                                  · linarith only [h6316, h8152, hlam]
                                                  · linarith only [h6314, h8152, hlam]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [hlam, p8118_0]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h7120, h7126, h7530, hc23, hc34, hlam, hphi, p8118_1]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h7118, hlam, p8118_0]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h7118, h7120, h7530, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8118_1, u0elo3]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h0, h6311, h7118, h7530, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8118_1]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [h7536, hlam, p8118_0]
                                                · have p8118_0 := h8118c.1
                                                  have p8118_1 := h8118c.2.1
                                                  have p8118_2 := h8118c.2.2.1
                                                  have p8118_3 := h8118c.2.2.2
                                                  linarith only [hlam, p8118_0]
                                              · linarith only [h8117, hlam, p8075_0]
                                            · linarith only [h6316, h8116, hlam]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      rcases p8075_3 (m.d 0 3) (by simp) with h8164 | h8164
                                      · linarith only [h6900, h8164, hlam]
                                      · linarith only [h6310, h8164, hlam]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      rcases p8075_3 (m.d 0 3) (by simp) with h8167 | h8167
                                      · linarith only [h6900, h8167, hlam]
                                      · linarith only [h6313, h8167, hlam]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [h7536, hlam, p8075_0]
                                    · have p8075_0 := h8075c.1
                                      have p8075_1 := h8075c.2.1
                                      have p8075_2 := h8075c.2.2.1
                                      have p8075_3 := h8075c.2.2.2
                                      linarith only [hlam, p8075_0]
                            · linarith only [h7121, h8068, hlam]
                          · linarith only [h8067, hlam, p8044_0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h6310, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7537_1, p8044_1]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [hlam, p8044_0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h0, h6310, h6311, h7118, hlam, p7537_1, p8044_2]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h0, h6311, h7118, h7126, hlam, p8044_2]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          rcases p8044_3 (m.d 0 1) (by simp) with h8178 | h8178
                          · linarith only [h0, h8178, hlam]
                          · linarith only [h6312, h8178, hlam]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h6310, hlam, p8044_0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h7119, hlam, p8044_1]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [hlam, p8044_0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h7122, hlam, p8044_1]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h7124, hlam, p8044_1]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h6311, hlam, p8044_0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h7120, hlam, p8044_1]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h6311, h7118, h7119, h7126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8044_1, u0elo0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [hlam, p8044_0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h7126, hlam, p8044_1]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h6312, hlam, p8044_0]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h7121, hlam, p8044_1]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h0, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8044_1]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [h0, h6311, h7118, h7126, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8044_1]
                        · have p8044_0 := h8044c.1
                          have p8044_1 := h8044c.2.1
                          have p8044_2 := h8044c.2.2.1
                          have p8044_3 := h8044c.2.2.2
                          linarith only [hlam, p8044_0]
                    · linarith only [h6900, h7585, hlam]
                  · linarith only [h6316, h7584, hlam]
              · linarith only [h6313, h7581, hlam]
            · linarith only [h6310, h7580, hlam]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [h7118, hlam, p7537_1]
          · have p7537_0 := h7537c.1
            have p7537_1 := h7537c.2.1
            have p7537_2 := h7537c.2.2.1
            have p7537_3 := h7537c.2.2.2
            linarith only [hlam, p7537_0]
        · linarith only [h0, h6310, h6311, h6316, h7118, h7119, h7536, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7120 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7121 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h7122 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h7124 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 1 4 5 (by decide) (by decide) with h7126 | h7126
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119 h7120 h7121 h7122 h7124 h7126
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119 h7120 h7121 h7122 h7124 h7126

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7120 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7121 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h7122 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 1 3 5 (by decide) (by decide) with h7124 | h7124
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119 h7120 h7121 h7122 h7124
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119 h7120 h7121 h7122 h7124

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7120 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7121 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 1 3 4 (by decide) (by decide) with h7122 | h7122
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119 h7120 h7121 h7122
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119 h7120 h7121 h7122

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7120 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7121 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h0, h6315, h7121, hlam]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7120 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 1 2 5 (by decide) (by decide) with h7121 | h7121
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119 h7120 h7121
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h7119 h7120 h7121

end R2N4
