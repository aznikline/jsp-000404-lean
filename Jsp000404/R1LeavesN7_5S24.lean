import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S22
import Jsp000404.R1LeavesN7_5S23

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11844 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11845 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11846 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11847 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h13714 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h13836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  have h11844 := hg11844
  have h11845 := hg11845
  have h11846 := hg11846
  rcases m.htr 1 2 3 (by decide) (by decide) with h14479 | h14479
  · rcases m.htr 1 2 4 (by decide) (by decide) with h14480 | h14480
    · rcases m.htr 1 2 5 (by decide) (by decide) with h14481 | h14481
      · rcases m.htr 1 3 4 (by decide) (by decide) with h14482 | h14482
        · rcases m.htr 1 3 5 (by decide) (by decide) with h14483 | h14483
          · rcases m.htr 1 4 5 (by decide) (by decide) with h14484 | h14484
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14485 | h14485
              · linarith only [h11844, h11847, h14485, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h14487 | h14487
                · linarith only [h11282, h11844, h11847, h13714, h13836, h14479, h14482, h14484, h14487, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14489 | h14489
                  · linarith only [h11845, h13836, h14489, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14491 | h14491
                    · linarith only [h11847, h13836, h14479, h14482, h14491, h6310, hc01, hc12, hlam, hphi]
                    · linarith only [h11847, h14479, h14482, h14484, h14491, h6310, hc01, hc12, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14494 | h14494
              · linarith only [h11844, h11847, h14494, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h14496 | h14496
                · linarith only [h11844, h13714, h14496, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14498 | h14498
                  · linarith only [h11845, h14484, h14498, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14500 | h14500
                    · linarith only [h14482, h14484, h14500, hlam]
                    · rcases h0bigk with h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c | h14502c
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [hlam, p14502_0]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h0, hlam, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h6310, hlam, p14502_0]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h9935, hlam, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h11282, hlam, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        rcases p14502_3 (m.d 0 1) (by simp) with h14508 | h14508
                        · linarith only [h0, h14508, hlam]
                        · rcases p14502_3 (m.d 0 2) (by simp) with h14510 | h14510
                          · rcases p14502_3 (m.d 0 3) (by simp) with h14511 | h14511
                            · linarith only [h11844, h14511, hlam]
                            · linarith only [h14511, h6310, hlam]
                          · linarith only [h0, h14510, hlam]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [hlam, p14502_0]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        rcases p14502_3 (m.d 0 1) (by simp) with h14516 | h14516
                        · linarith only [h0, h14516, hlam]
                        · rcases p14502_3 (m.d 0 2) (by simp) with h14518 | h14518
                          · rcases p14502_3 (m.d 0 3) (by simp) with h14519 | h14519
                            · linarith only [h11844, h14519, hlam]
                            · rcases p14502_3 (m.d 0 4) (by simp) with h14521 | h14521
                              · linarith only [h11845, h14521, hlam]
                              · linarith only [h11847, h14521, hlam]
                          · linarith only [h11844, h14518, hlam]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        rcases p14502_3 (m.d 0 1) (by simp) with h14525 | h14525
                        · linarith only [h0, h14525, hlam]
                        · rcases p14502_3 (m.d 0 2) (by simp) with h14527 | h14527
                          · rcases p14502_3 (m.d 0 3) (by simp) with h14528 | h14528
                            · linarith only [h11844, h14528, hlam]
                            · rcases p14502_3 (m.d 0 4) (by simp) with h14530 | h14530
                              · linarith only [h11845, h14530, hlam]
                              · rcases p14502_3 (m.d 0 5) (by simp) with h14532 | h14532
                                · linarith only [h11846, h14532, hlam]
                                · linarith only [h13836, h14532, hlam]
                          · linarith only [h11845, h14527, hlam]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        rcases p14502_3 (m.d 0 1) (by simp) with h14536 | h14536
                        · linarith only [h0, h14536, hlam]
                        · rcases p14502_3 (m.d 0 2) (by simp) with h14538 | h14538
                          · rcases p14502_3 (m.d 0 3) (by simp) with h14539 | h14539
                            · linarith only [h11844, h14539, hlam]
                            · rcases p14502_3 (m.d 0 4) (by simp) with h14541 | h14541
                              · linarith only [h11845, h14541, hlam]
                              · rcases p14502_3 (m.d 0 5) (by simp) with h14543 | h14543
                                · linarith only [h11846, h14543, hlam]
                                · rcases h0emin with h14545 | h14545 | h14545 | h14545 | h14545
                                  · linarith only [h11847, h14482, h14484, h14545, h6310, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · rcases h1bigk with h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c | h14547c
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [hlam, p14547_0]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h0, hlam, p14547_0]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h6310, hlam, p14547_0]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h9935, hlam, p14547_0]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h11282, hlam, p14547_0]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      rcases p14547_3 (m.d 0 1) (by simp) with h14553 | h14553
                                      · linarith only [h14553, hlam, p14547_0]
                                      · rcases p14547_3 (m.d 1 2) (by simp) with h14555 | h14555
                                        · rcases p14547_3 (m.d 1 3) (by simp) with h14556 | h14556
                                          · linarith only [h14479, h14556, hlam]
                                          · linarith only [h14556, h6310, hlam]
                                        · linarith only [h14555, hlam, p14547_0]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [hlam, p14547_0]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p14547_1]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p14547_1]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p14547_1]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      rcases p14547_3 (m.d 0 1) (by simp) with h14564 | h14564
                                      · linarith only [h14564, hlam, p14547_0]
                                      · rcases p14547_3 (m.d 1 2) (by simp) with h14566 | h14566
                                        · rcases p14547_3 (m.d 1 3) (by simp) with h14567 | h14567
                                          · rcases p14547_3 (m.d 1 4) (by simp) with h14568 | h14568
                                            · linarith only [h14482, h14568, hlam]
                                            · linarith only [h14568, h9935, hlam]
                                          · linarith only [h14567, hlam, p14547_0]
                                        · linarith only [h0, h14566, hlam]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h14479, hlam, p14547_1]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [hlam, p14547_0]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h11847, h14482, h6310, hc01, hc13, hlam, hphi, p14547_1]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h11847, h14479, h14483, h14500, h6310, hc01, hc12, hlam, hphi, p14547_1]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h14484, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14547_1]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h14480, hlam, p14547_1]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h14482, hlam, p14547_0]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [hlam, p14547_0]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h14484, hlam, p14547_1]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      rcases p14547_3 (m.d 0 1) (by simp) with h14582 | h14582
                                      · linarith only [h14582, hlam, p14547_0]
                                      · rcases p14547_3 (m.d 1 2) (by simp) with h14584 | h14584
                                        · rcases p14547_3 (m.d 1 3) (by simp) with h14585 | h14585
                                          · rcases p14547_3 (m.d 1 4) (by simp) with h14586 | h14586
                                            · linarith only [h14484, h14586, hlam]
                                            · linarith only [h14586, h9935, hlam]
                                          · linarith only [h14585, h6310, hlam]
                                        · linarith only [h0, h14584, hlam]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h14481, hlam, p14547_1]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h14483, hlam, p14547_0]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [h9935, hc01, hc15, hlam, hphi, p14547_1]
                                    · have p14547_0 := h14547c.1
                                      have p14547_1 := h14547c.2.1
                                      have p14547_2 := h14547c.2.2.1
                                      have p14547_3 := h14547c.2.2.2
                                      linarith only [hlam, p14547_0]
                                  · linarith only [h11847, h13836, h14545, hlam, p14502_1, u0elo1]
                                  · linarith only [h13836, h14545, hlam, p14502_1, u0elo1]
                                  · linarith only [h14545, hlam, p14502_1, u0elo1]
                          · linarith only [h11846, h14538, hlam]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h11847, hc01, hc34, hlam, hphi, ht12, ht23, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h11844, hlam, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [hlam, p14502_0]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h11847, hlam, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h13714, hlam, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h13836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h11845, hlam, p14502_0]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h13836, h6310, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [hlam, p14502_0]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h13836, hlam, p14502_0]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h13714, h14479, h14483, hc01, hc12, hlam, hphi, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h11846, hlam, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h13714, h14479, h14483, h6310, hc01, hc12, hlam, hphi, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [h13714, h14479, h14483, h9935, hc01, hc12, hlam, hphi, p14502_1]
                      · have p14502_0 := h14502c.1
                        have p14502_1 := h14502c.2.1
                        have p14502_2 := h14502c.2.2.1
                        have p14502_3 := h14502c.2.2.2
                        linarith only [hlam, p14502_0]
          · linarith only [h11847, h14482, h14483, h6310, hc01, hc35, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h14615 | h14615
          · linarith only [h13714, h14482, h14615, h6310, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h14617 | h14617
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14618 | h14618
              · linarith only [h11844, h11847, h14618, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h14620 | h14620
                · linarith only [h11844, h14615, h14620, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14622 | h14622
                  · linarith only [h11845, h13836, h14622, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14624 | h14624
                    · rcases h0bigk with h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [hlam, p14625_0]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h0, hlam, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h6310, hlam, p14625_0]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h9935, hlam, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h11282, hlam, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        rcases p14625_3 (m.d 0 1) (by simp) with h14631 | h14631
                        · linarith only [h0, h14631, hlam]
                        · rcases p14625_3 (m.d 0 2) (by simp) with h14633 | h14633
                          · rcases p14625_3 (m.d 0 3) (by simp) with h14634 | h14634
                            · linarith only [h11844, h14634, hlam]
                            · linarith only [h14634, h6310, hlam]
                          · linarith only [h0, h14633, hlam]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [hlam, p14625_0]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        rcases p14625_3 (m.d 0 1) (by simp) with h14639 | h14639
                        · linarith only [h0, h14639, hlam]
                        · rcases p14625_3 (m.d 0 2) (by simp) with h14641 | h14641
                          · rcases p14625_3 (m.d 0 3) (by simp) with h14642 | h14642
                            · linarith only [h11844, h14642, hlam]
                            · rcases p14625_3 (m.d 0 4) (by simp) with h14644 | h14644
                              · linarith only [h11845, h14644, hlam]
                              · linarith only [h11847, h14644, hlam]
                          · linarith only [h11844, h14641, hlam]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        rcases p14625_3 (m.d 0 1) (by simp) with h14648 | h14648
                        · linarith only [h0, h14648, hlam]
                        · rcases p14625_3 (m.d 0 2) (by simp) with h14650 | h14650
                          · rcases p14625_3 (m.d 0 3) (by simp) with h14651 | h14651
                            · linarith only [h11844, h14651, hlam]
                            · rcases p14625_3 (m.d 0 4) (by simp) with h14653 | h14653
                              · linarith only [h11845, h14653, hlam]
                              · rcases p14625_3 (m.d 0 5) (by simp) with h14655 | h14655
                                · linarith only [h11846, h14655, hlam]
                                · linarith only [h13836, h14655, hlam]
                          · linarith only [h11845, h14650, hlam]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        rcases p14625_3 (m.d 0 1) (by simp) with h14659 | h14659
                        · linarith only [h0, h14659, hlam]
                        · rcases p14625_3 (m.d 0 2) (by simp) with h14661 | h14661
                          · rcases p14625_3 (m.d 0 3) (by simp) with h14662 | h14662
                            · linarith only [h11844, h14662, hlam]
                            · rcases p14625_3 (m.d 0 4) (by simp) with h14664 | h14664
                              · linarith only [h11845, h14664, hlam]
                              · rcases p14625_3 (m.d 0 5) (by simp) with h14666 | h14666
                                · linarith only [h11846, h14666, hlam]
                                · rcases h0emin with h14668 | h14668 | h14668 | h14668 | h14668
                                  · linarith only [h11847, h13836, h14668, h6310, hlam, p14625_1, u0elo1]
                                  · rcases h1bigk with h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c | h14670c
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [hlam, p14670_0]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h0, hlam, p14670_0]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h6310, hlam, p14670_0]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h9935, hlam, p14670_0]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h11282, hlam, p14670_0]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      rcases p14670_3 (m.d 0 1) (by simp) with h14676 | h14676
                                      · linarith only [h14676, hlam, p14670_0]
                                      · rcases p14670_3 (m.d 1 2) (by simp) with h14678 | h14678
                                        · rcases p14670_3 (m.d 1 3) (by simp) with h14679 | h14679
                                          · linarith only [h14479, h14679, hlam]
                                          · linarith only [h14679, h6310, hlam]
                                        · linarith only [h14678, hlam, p14670_0]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [hlam, p14670_0]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h14615, hc01, hc35, hlam, hphi, ht12, ht23, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h14479, hlam, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [hlam, p14670_0]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h14482, hlam, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h14615, hlam, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      rcases p14670_3 (m.d 0 1) (by simp) with h14692 | h14692
                                      · linarith only [h14692, hlam, p14670_0]
                                      · rcases p14670_3 (m.d 1 2) (by simp) with h14694 | h14694
                                        · rcases p14670_3 (m.d 1 3) (by simp) with h14695 | h14695
                                          · linarith only [h14482, h14695, hlam]
                                          · linarith only [h14695, h6310, hlam]
                                        · linarith only [h0, h14694, hlam]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h14480, hlam, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h6310, hc01, hc14, hlam, hphi, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [hlam, p14670_0]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h11847, h13836, h14482, h14617, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      rcases p14670_3 (m.d 0 1) (by simp) with h14703 | h14703
                                      · linarith only [h14703, hlam, p14670_0]
                                      · rcases p14670_3 (m.d 1 2) (by simp) with h14705 | h14705
                                        · rcases p14670_3 (m.d 1 3) (by simp) with h14706 | h14706
                                          · linarith only [h14615, h14706, hlam]
                                          · linarith only [h14706, h6310, hlam]
                                        · linarith only [h0, h14705, hlam]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h14481, hlam, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h6310, hc01, hc15, hlam, hphi, p14670_1]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [h14617, hlam, p14670_0]
                                    · have p14670_0 := h14670c.1
                                      have p14670_1 := h14670c.2.1
                                      have p14670_2 := h14670c.2.2.1
                                      have p14670_3 := h14670c.2.2.2
                                      linarith only [hlam, p14670_0]
                                  · linarith only [h11847, h13836, h14668, hlam, p14625_1, u0elo1]
                                  · linarith only [h13836, h14668, hlam, p14625_1, u0elo1]
                                  · linarith only [h14668, hlam, p14625_1, u0elo1]
                          · linarith only [h11846, h14661, hlam]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h11847, h13836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h11844, hlam, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [hlam, p14625_0]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h11847, hlam, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h13714, hlam, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h13836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h11845, hlam, p14625_0]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h13836, hc03, hc45, hlam, hphi, ht34, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [hlam, p14625_0]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h13836, hlam, p14625_0]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h13836, h14482, h14617, hc01, hc34, hlam, hphi, ht12, ht23, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h11846, hlam, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h13836, h14482, h14617, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [h13836, h14482, h14617, h9935, hc01, hc34, hlam, hphi, ht12, ht23, p14625_1]
                      · have p14625_0 := h14625c.1
                        have p14625_1 := h14625c.2.1
                        have p14625_2 := h14625c.2.2.1
                        have p14625_3 := h14625c.2.2.2
                        linarith only [hlam, p14625_0]
                    · linarith only [h14482, h14617, h14624, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14734 | h14734
              · linarith only [h11844, h11847, h14734, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h14736 | h14736
                · linarith only [h11844, h13714, h14736, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14738 | h14738
                  · linarith only [h11845, h14482, h14617, h14738, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14740 | h14740
                    · linarith only [h14482, h14617, h14740, h6310, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h14482, h14740, h6310, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
      · linarith only [h0, h11846, h14481, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
    · linarith only [h0, h11845, h14480, hlam]
  · linarith only [h0, h11844, h14479, hlam]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11844 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11845 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11846 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11847 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h13714 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  have h11844 := hg11844
  have h11845 := hg11845
  have h11846 := hg11846
  rcases m.htr 0 4 5 (by decide) (by decide) with h13836 | h13836
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h13714 h13836
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h13714 h13836

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11844 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11845 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11846 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11847 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  have h11844 := hg11844
  have h11845 := hg11845
  have h11846 := hg11846
  rcases m.htr 0 3 5 (by decide) (by decide) with h13714 | h13714
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h13714
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h13714

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11844 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11845 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11846 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  have h11844 := hg11844
  have h11845 := hg11845
  have h11846 := hg11846
  rcases m.htr 0 3 4 (by decide) (by decide) with h11847 | h11847
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847

set_option maxHeartbeats 6056000 in
set_option maxHeartbeats 6056000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s18 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11844 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11845 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  have h11844 := hg11844
  have h11845 := hg11845
  rcases m.htr 0 2 5 (by decide) (by decide) with h11846 | h11846
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19 m hb0 hb1 hb3 hb4 h0 h6310 h9935 h11282 h11844 h11845 h11846
  · rcases m.htr 0 3 4 (by decide) (by decide) with h14746 | h14746
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14747 | h14747
      · linarith only [h11844, h11846, h14747, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14749 | h14749
        · linarith only [h11845, h11846, h14749, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14751 | h14751
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14752 | h14752
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14753 | h14753
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14754 | h14754
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14755 | h14755
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14756 | h14756
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14757 | h14757
                      · linarith only [h11844, h11846, h14753, h14757, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h11844, h11846, h14746, h14753, h14757, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14760 | h14760
                      · linarith only [h11844, h11846, h14753, h14760, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h11844, h11846, h14746, h14753, h14760, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14763 | h14763
                    · linarith only [h14749, h14754, h14755, h14763, h9935, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14765 | h14765
                      · linarith only [h11844, h11846, h14753, h14765, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h11844, h11846, h14746, h14753, h14765, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h11844, h11846, h14746, h14753, h14754, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14769 | h14769
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14770 | h14770
                  · linarith only [h14746, h14747, h14751, h14753, h14770, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14772 | h14772
                    · linarith only [h14749, h14752, h14753, h14772, h9935, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14774 | h14774
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14775 | h14775
                        · linarith only [h11844, h14770, h14775, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14777 | h14777
                          · linarith only [h14772, h14777, h9935, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h11844, h14753, h14774, h14777, hc34, hc45, hlam, hphi]
                      · linarith only [h14746, h14747, h14774, hc23, hc35, hlam, hphi]
                · linarith only [h14746, h14769, h6310, hlam]
            · linarith only [h0, h11845, h14752, hlam]
          · linarith only [h0, h11844, h14751, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14784 | h14784
      · linarith only [h11844, h11846, h14784, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14786 | h14786
        · linarith only [h11845, h11846, h14786, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14788 | h14788
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14789 | h14789
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14790 | h14790
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14791 | h14791
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14792 | h14792
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14793 | h14793
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14794 | h14794
                      · linarith only [h11844, h11846, h14746, h14790, h14794, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14796 | h14796
                        · linarith only [h11845, h11846, h14784, h14790, h14794, h14796, h6310, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14798 | h14798
                          · linarith only [h11845, h11846, h14788, h14792, h14796, h14798, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14800 | h14800
                            · linarith only [h11845, h11846, h14794, h14798, h14800, hc23, hc34, hlam, hphi]
                            · linarith only [h14746, h14788, h14791, h14793, h14800, h6310, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14803 | h14803
                      · linarith only [h11844, h11846, h14746, h14803, h6310, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14805 | h14805
                        · linarith only [h11845, h11846, h14784, h14790, h14803, h14805, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14807 | h14807
                          · linarith only [h11845, h11846, h14788, h14792, h14793, h14805, h14807, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14809 | h14809
                            · linarith only [h14791, h14793, h14809, hlam]
                            · rcases h0bigk with h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c | h14811c
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [hlam, p14811_0]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h0, hlam, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h6310, hlam, p14811_0]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h9935, hlam, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11282, hlam, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11846, h14788, h14792, h14805, hc01, hc12, hlam, hphi, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [hlam, p14811_0]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11846, h14788, h14792, h14805, h6310, hc01, hc12, hlam, hphi, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11846, h14788, h14792, h14805, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11846, hlam, p14811_0]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h14746, h14791, hc01, hc14, hlam, hphi, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11844, hlam, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [hlam, p14811_0]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h14746, hlam, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h14784, hlam, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11845, h11846, h14788, h14792, h14793, h14803, h14805, h9935, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11845, hlam, p14811_0]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11845, h11846, h14788, h14792, h14805, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [hlam, p14811_0]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h14786, hlam, p14811_0]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11846, h14788, h14792, h14805, hc01, hc12, hlam, hphi, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11845, h11846, h14788, h14792, h14803, h14805, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11846, h14788, h14792, h14805, h6310, hc01, hc12, hlam, hphi, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [h11846, h14788, h14792, h14805, h9935, hc01, hc12, hlam, hphi, p14811_1]
                              · have p14811_0 := h14811c.1
                                have p14811_1 := h14811c.2.1
                                have p14811_2 := h14811c.2.2.1
                                have p14811_3 := h14811c.2.2.2
                                linarith only [hlam, p14811_0]
                  · linarith only [h14746, h14791, h14792, h6310, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14838 | h14838
                  · linarith only [h14784, h14791, h14838, h6310, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14840 | h14840
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14841 | h14841
                      · linarith only [h11844, h14791, h14841, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14843 | h14843
                        · linarith only [h11845, h11846, h14790, h14841, h14843, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14845 | h14845
                          · linarith only [h11845, h11846, h14746, h14786, h14790, h14845, h6310, hc01, hc12, hlam, hphi]
                          · linarith only [h11845, h11846, h14791, h14840, h14841, h14845, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14848 | h14848
                      · linarith only [h14791, h14848, h6310, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14850 | h14850
                        · linarith only [h11844, h11846, h14790, h14850, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14852 | h14852
                          · linarith only [h11845, h11846, h14790, h14791, h14840, h14852, h6310, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14854 | h14854
                            · linarith only [h14791, h14840, h14854, h6310, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h14791, h14854, h6310, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14857 | h14857
                · linarith only [h14746, h14788, h14790, h14857, h6310, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14859 | h14859
                  · linarith only [h14784, h14789, h14790, h14857, h14859, h6310, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14861 | h14861
                    · linarith only [h14746, h14786, h14789, h14790, h14861, h6310, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14863 | h14863
                      · linarith only [h11844, h14857, h14863, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14865 | h14865
                        · linarith only [h0, h11282, h11845, h14790, h14859, h14863, h14865, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14867 | h14867
                          · linarith only [h0, h11845, h14786, h14790, h14865, h14867, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14869 | h14869
                            · linarith only [h0, h11845, h14790, h14863, h14867, h14869, hc23, hc34, hlam, hphi]
                            · linarith only [h14857, h14869, h6310, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h11845, h14789, hlam]
          · linarith only [h0, h11844, h14788, hlam]

set_option maxHeartbeats 6858000 in
set_option maxHeartbeats 6858000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s17 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11844 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  have h11844 := hg11844
  rcases m.htr 0 2 4 (by decide) (by decide) with h11845 | h11845
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s18 m hb0 hb1 hb3 hb4 h0 h6310 h9935 h11282 h11844 h11845
  · rcases m.htr 0 2 5 (by decide) (by decide) with h14874 | h14874
    · rcases m.htr 0 3 4 (by decide) (by decide) with h14875 | h14875
      · linarith only [h11844, h11845, h14875, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h14877 | h14877
        · rcases m.htr 0 4 5 (by decide) (by decide) with h14878 | h14878
          · rcases m.htr 1 2 3 (by decide) (by decide) with h14879 | h14879
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14880 | h14880
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14881 | h14881
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14882 | h14882
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14883 | h14883
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14884 | h14884
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14885 | h14885
                        · linarith only [h11282, h11844, h14875, h14877, h14885, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14887 | h14887
                          · linarith only [h11844, h11845, h14879, h14882, h14885, h14887, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h11844, h11845, h14877, h14879, h14882, h14885, h14887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h11845, h14874, h14878, h14884, h9935, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h11844, h11845, h14877, h14880, h14883, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14892 | h14892
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14893 | h14893
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14894 | h14894
                        · linarith only [h11844, h11845, h14880, h14882, h14894, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14896 | h14896
                          · linarith only [h11844, h11845, h14880, h14896, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h11844, h11845, h14877, h14880, h14896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h11845, h14878, h14880, h14893, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h14877, h14892, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h11845, h14880, h14881, hc02, hc25, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14902 | h14902
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14903 | h14903
                  · linarith only [h14875, h14877, h14879, h14880, h14903, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14905 | h14905
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14906 | h14906
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14907 | h14907
                        · linarith only [h11844, h14903, h14907, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14909 | h14909
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14910 | h14910
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14911 | h14911
                              · rcases h0bigk with h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [hlam, p14912_0]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h0, hlam, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h6310, hlam, p14912_0]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h9935, hlam, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h11282, hlam, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h0, h14880, h14907, hc01, hc34, hlam, hphi, ht12, ht23, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [hlam, p14912_0]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h0, h11844, h14880, h14907, h14909, h14911, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h11845, hlam, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h0, h11282, h14880, h14907, hc01, hc34, hlam, hphi, ht12, ht23, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h0, h11844, h14880, h14907, hc01, hc34, hlam, hphi, ht12, ht23, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h11844, hlam, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [hlam, p14912_0]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h14875, hlam, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h0, h11282, h11844, h14880, h14907, hc01, hc34, hlam, hphi, ht12, ht23, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  rcases p14912_3 (m.d 0 1) (by simp) with h14928 | h14928
                                  · linarith only [h14928, h9935, hlam]
                                  · rcases p14912_3 (m.d 0 2) (by simp) with h14930 | h14930
                                    · linarith only [h11845, h14930, hlam]
                                    · linarith only [h0, h14930, hlam]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h11844, h14909, h14911, hc45, hlam, hphi, ht0b, ht5b, p14912_1, u0elo3]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h11844, h14909, h14911, hc45, hlam, hphi, ht0b, ht5b, p14912_1, u0elo3]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [hlam, p14912_0]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  rcases p14912_3 (m.d 0 1) (by simp) with h14936 | h14936
                                  · linarith only [h14936, h9935, hlam]
                                  · rcases p14912_3 (m.d 0 2) (by simp) with h14938 | h14938
                                    · linarith only [h11845, h14938, hlam]
                                    · linarith only [h14874, h14938, hlam]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h0, h14874, h14880, h14907, hc01, hc34, hlam, hphi, ht12, ht23, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h14874, hlam, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h14877, hlam, p14912_0]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [h14878, hlam, p14912_1]
                                · have p14912_0 := h14912c.1
                                  have p14912_1 := h14912c.2.1
                                  have p14912_2 := h14912c.2.2.1
                                  have p14912_3 := h14912c.2.2.2
                                  linarith only [hlam, p14912_0]
                              · linarith only [h0, h11844, h14880, h14907, h14909, h14911, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h11844, h14877, h14878, h14880, h14910, hlam]
                          · linarith only [h0, h11844, h14877, h14880, h14907, h14909, hc23, hc34, hlam, hphi]
                      · linarith only [h14878, h14906, h9935, hlam]
                    · linarith only [h14877, h14905, h6310, hlam]
                · linarith only [h0, h14874, h14902, hlam]
            · linarith only [h0, h11844, h14879, hlam]
          · linarith only [h11844, h11845, h14877, h14878, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h14954 | h14954
          · rcases m.htr 1 2 3 (by decide) (by decide) with h14955 | h14955
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14956 | h14956
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14957 | h14957
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14958 | h14958
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14959 | h14959
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14960 | h14960
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14961 | h14961
                        · linarith only [h11844, h11845, h14875, h14956, h14961, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14963 | h14963
                          · linarith only [h11844, h11845, h14877, h14955, h14958, h14961, h14963, h6310, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14965 | h14965
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14966 | h14966
                              · rcases h0bigk with h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c | h14967c
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [hlam, p14967_0]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h0, hlam, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h6310, hlam, p14967_0]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h9935, hlam, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11282, hlam, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11845, h14955, h14958, h14961, hc01, hc12, hlam, hphi, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [hlam, p14967_0]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11845, h14955, h14958, h14961, h6310, hc01, hc12, hlam, hphi, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11845, hlam, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11845, h14955, h14958, h14961, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h14877, h14959, hc01, hc15, hlam, hphi, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11844, hlam, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [hlam, p14967_0]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h14875, hlam, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h14877, hlam, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11845, h14955, h14958, h14961, hc01, hc12, hlam, hphi, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11845, h14874, h14955, h14958, h14961, h14963, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11845, h14955, h14958, h14961, h6310, hc01, hc12, hlam, hphi, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [hlam, p14967_0]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11845, h14877, h14955, h14958, h14961, h6310, hc01, hc12, hlam, hphi, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11845, h14874, h14955, h14958, h14961, hc01, hc12, hlam, hphi, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h14874, hlam, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h11845, h14874, h14955, h14958, h14961, h6310, hc01, hc12, hlam, hphi, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [h14954, hlam, p14967_1]
                                · have p14967_0 := h14967c.1
                                  have p14967_1 := h14967c.2.1
                                  have p14967_2 := h14967c.2.2.1
                                  have p14967_3 := h14967c.2.2.2
                                  linarith only [hlam, p14967_0]
                              · linarith only [h11844, h11845, h14961, h14966, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h11845, h14874, h14954, h14965, hlam]
                      · linarith only [h11845, h14874, h14954, h14960, h9935, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h14875, h14958, h14959, h6310, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14997 | h14997
                    · linarith only [h14877, h14958, h14997, h6310, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14999 | h14999
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h15000 | h15000
                        · linarith only [h14958, h15000, h6310, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15002 | h15002
                          · linarith only [h11844, h11845, h14956, h14997, h15002, h6310, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h15004 | h15004
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h15005 | h15005
                              · rcases h0bigk with h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c | h15006c
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [hlam, p15006_0]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h0, hlam, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h6310, hlam, p15006_0]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h9935, hlam, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11282, hlam, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11845, h14956, hc01, hc12, hlam, hphi, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [hlam, p15006_0]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11845, h14956, h6310, hc01, hc12, hlam, hphi, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11845, hlam, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11845, h14956, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h14997, h6310, hc01, hc35, hlam, hphi, ht12, ht23, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11844, hlam, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [hlam, p15006_0]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h14875, hlam, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h14877, hlam, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11845, h14956, hc01, hc12, hlam, hphi, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11845, h14874, h14956, h15002, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11845, h14956, h6310, hc01, hc12, hlam, hphi, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [hlam, p15006_0]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11845, h14877, h14956, h6310, hc01, hc12, hlam, hphi, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11845, h14874, h14956, hc01, hc12, hlam, hphi, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h14874, hlam, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h11845, h14874, h14956, h6310, hc01, hc12, hlam, hphi, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [h14954, hlam, p15006_1]
                                · have p15006_0 := h15006c.1
                                  have p15006_1 := h15006c.2.1
                                  have p15006_2 := h15006c.2.2.1
                                  have p15006_3 := h15006c.2.2.2
                                  linarith only [hlam, p15006_0]
                              · linarith only [h14958, h15005, h6310, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h11845, h14874, h14954, h15004, hlam]
                      · linarith only [h11845, h14874, h14954, h14956, h14999, hlam]
                · linarith only [h11845, h14874, h14956, h14957, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h15036 | h15036
                · rcases m.htr 1 3 4 (by decide) (by decide) with h15037 | h15037
                  · linarith only [h14875, h14955, h14956, h15037, h6310, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h15039 | h15039
                    · linarith only [h14877, h15037, h15039, hc03, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h15041 | h15041
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h15042 | h15042
                        · linarith only [h11844, h15037, h15042, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15044 | h15044
                          · linarith only [h0, h11844, h14956, h15039, h15042, h15044, h6310, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h15046 | h15046
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h15047 | h15047
                              · rcases h0bigk with h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c | h15048c
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [hlam, p15048_0]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h0, hlam, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h6310, hlam, p15048_0]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h9935, hlam, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h11282, hlam, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h0, h14956, h15042, hc01, hc34, hlam, hphi, ht12, ht23, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [hlam, p15048_0]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h0, h14956, h15042, hc03, hc34, hlam, hphi, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h11845, hlam, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h0, h11282, h14956, h15042, hc01, hc34, hlam, hphi, ht12, ht23, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h15039, h6310, hc01, hc35, hlam, hphi, ht12, ht23, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h11844, hlam, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [hlam, p15048_0]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h14875, hlam, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h14877, hlam, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  rcases p15048_3 (m.d 0 1) (by simp) with h15064 | h15064
                                  · linarith only [h15064, h9935, hlam]
                                  · rcases p15048_3 (m.d 0 2) (by simp) with h15066 | h15066
                                    · linarith only [h11845, h15066, hlam]
                                    · linarith only [h0, h15066, hlam]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h14874, h15044, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15048_1, u0elo3]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  rcases p15048_3 (m.d 0 1) (by simp) with h15070 | h15070
                                  · linarith only [h15070, h9935, hlam]
                                  · rcases p15048_3 (m.d 0 2) (by simp) with h15072 | h15072
                                    · linarith only [h11845, h15072, hlam]
                                    · linarith only [h11844, h15072, hlam]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [hlam, p15048_0]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  rcases p15048_3 (m.d 0 1) (by simp) with h15076 | h15076
                                  · linarith only [h15076, h9935, hlam]
                                  · rcases p15048_3 (m.d 0 2) (by simp) with h15078 | h15078
                                    · linarith only [h11845, h15078, hlam]
                                    · linarith only [h14874, h15078, hlam]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h11282, h14956, h15036, h15042, hc01, hc34, hlam, hphi, ht12, ht23, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h14874, hlam, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h11282, h14956, h15036, h15042, hc03, hc34, hlam, hphi, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [h14954, hlam, p15048_1]
                                · have p15048_0 := h15048c.1
                                  have p15048_1 := h15048c.2.1
                                  have p15048_2 := h15048c.2.2.1
                                  have p15048_3 := h15048c.2.2.2
                                  linarith only [hlam, p15048_0]
                              · linarith only [h0, h14956, h15042, h15047, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h11282, h14954, h14956, h15036, h15046, hlam]
                      · linarith only [h11282, h14954, h14956, h15036, h15041, h9935, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h14874, h14955, h15036, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h11844, h14955, hlam]
          · linarith only [h11845, h14874, h14954, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h15092 | h15092
      · linarith only [h11844, h11845, h15092, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h15094 | h15094
        · linarith only [h11844, h14874, h15094, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h15096 | h15096
          · rcases m.htr 1 2 3 (by decide) (by decide) with h15097 | h15097
            · rcases m.htr 1 2 4 (by decide) (by decide) with h15098 | h15098
              · rcases m.htr 1 2 5 (by decide) (by decide) with h15099 | h15099
                · rcases m.htr 1 3 4 (by decide) (by decide) with h15100 | h15100
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h15101 | h15101
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h15102 | h15102
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h15103 | h15103
                        · linarith only [h11844, h11845, h15092, h15098, h15103, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15105 | h15105
                          · linarith only [h11844, h11845, h15094, h15097, h15100, h15103, h15105, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h15107 | h15107
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h15108 | h15108
                              · rcases h0bigk with h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c | h15109c
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [hlam, p15109_0]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h0, hlam, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h6310, hlam, p15109_0]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h9935, hlam, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h11282, hlam, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h14874, h15097, h15100, h15103, h15107, hc01, hc12, hlam, hphi, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [hlam, p15109_0]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h14874, h15097, h15100, h15103, h15107, h6310, hc01, hc12, hlam, hphi, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h11845, hlam, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h14874, hlam, p15109_0]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h11844, h14874, h15097, h15100, h15103, h15107, hc01, hc12, hlam, hphi, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h11844, hlam, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [hlam, p15109_0]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h15092, hlam, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h15094, hlam, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h11845, h15097, h15100, h15103, hc01, hc12, hlam, hphi, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h11844, h11845, h15097, h15100, h15103, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h11845, h15097, h15100, h15103, h6310, hc01, hc12, hlam, hphi, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [hlam, p15109_0]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h11844, h11845, h14874, h15097, h15100, h15103, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h14874, h15097, h15100, h15103, h15107, hc01, hc12, hlam, hphi, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h11844, h14874, h15097, h15100, h15103, h15107, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h14874, h15097, h15100, h15103, h15107, h6310, hc01, hc12, hlam, hphi, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [h15096, hlam, p15109_1]
                                · have p15109_0 := h15109c.1
                                  have p15109_1 := h15109c.2.1
                                  have p15109_2 := h15109c.2.2.1
                                  have p15109_3 := h15109c.2.2.2
                                  linarith only [hlam, p15109_0]
                              · linarith only [h11845, h15096, h15103, h15108, hlam]
                            · linarith only [h11845, h15096, h15107, hlam]
                      · linarith only [h15096, h15102, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h11844, h11845, h15092, h15100, h15101, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h15139 | h15139
                    · linarith only [h15094, h15100, h15139, h6310, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h15141 | h15141
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h15142 | h15142
                        · linarith only [h11844, h15100, h15142, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15144 | h15144
                          · linarith only [h11844, h14874, h15099, h15139, h15144, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h15146 | h15146
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h15147 | h15147
                              · rcases h0bigk with h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c | h15148c
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [hlam, p15148_0]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h0, hlam, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h6310, hlam, p15148_0]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h9935, hlam, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h11282, hlam, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h14874, h15098, h15146, hc01, hc12, hlam, hphi, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [hlam, p15148_0]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h14874, h15098, h15146, h6310, hc01, hc12, hlam, hphi, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h11845, hlam, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h14874, hlam, p15148_0]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h11844, h14874, h15098, h15146, hc01, hc12, hlam, hphi, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h11844, hlam, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [hlam, p15148_0]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h15092, hlam, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h15094, hlam, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h11845, h15098, hc01, hc12, hlam, hphi, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h11844, h11845, h15098, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h11845, h15098, h6310, hc01, hc12, hlam, hphi, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [hlam, p15148_0]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h11844, h11845, h14874, h15098, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h14874, h15098, h15146, hc01, hc12, hlam, hphi, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h11844, h14874, h15098, h15146, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h14874, h15098, h15146, h6310, hc01, hc12, hlam, hphi, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [h15096, hlam, p15148_1]
                                · have p15148_0 := h15148c.1
                                  have p15148_1 := h15148c.2.1
                                  have p15148_2 := h15148c.2.2.1
                                  have p15148_3 := h15148c.2.2.2
                                  linarith only [hlam, p15148_0]
                              · linarith only [h11845, h15096, h15098, h15100, h15147, hlam]
                            · linarith only [h11845, h15096, h15146, hlam]
                      · linarith only [h11845, h15096, h15098, h15141, hlam]
                · linarith only [h11844, h11845, h15098, h15099, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h15178 | h15178
                · linarith only [h11844, h14874, h15098, h15178, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h15180 | h15180
                  · linarith only [h15092, h15097, h15098, h15180, h6310, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h15182 | h15182
                    · linarith only [h15094, h15180, h15182, h6310, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h15184 | h15184
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h15185 | h15185
                        · linarith only [h11844, h15180, h15185, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15187 | h15187
                          · linarith only [h0, h11282, h11844, h15098, h15182, h15185, h15187, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h15189 | h15189
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h15190 | h15190
                              · rcases h0bigk with h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [hlam, p15191_0]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h0, hlam, p15191_1]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h6310, hlam, p15191_0]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h9935, hlam, p15191_1]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h11282, hlam, p15191_1]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h0, h15178, h15185, h15189, hc01, hc34, hlam, hphi, ht12, ht23, p15191_1]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [hlam, p15191_0]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h0, h15178, h15185, h15189, hc03, hc34, hlam, hphi, p15191_1]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h11845, hlam, p15191_1]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h14874, hlam, p15191_0]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h0, h11844, h15178, h15185, h15189, hc01, hc34, hlam, hphi, ht12, ht23, p15191_1]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h11844, hlam, p15191_1]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [hlam, p15191_0]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h15092, hlam, p15191_1]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h15094, hlam, p15191_1]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  rcases p15191_3 (m.d 0 1) (by simp) with h15207 | h15207
                                  · linarith only [h15207, h9935, hlam]
                                  · rcases p15191_3 (m.d 0 2) (by simp) with h15209 | h15209
                                    · linarith only [h11845, h15209, hlam]
                                    · linarith only [h0, h15209, hlam]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h11844, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15191_1, u0elo3]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  rcases p15191_3 (m.d 0 1) (by simp) with h15213 | h15213
                                  · linarith only [h15213, h9935, hlam]
                                  · rcases p15191_3 (m.d 0 2) (by simp) with h15215 | h15215
                                    · linarith only [h11845, h15215, hlam]
                                    · linarith only [h11844, h15215, hlam]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [hlam, p15191_0]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h11844, h14874, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15191_1, u0elo3]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  rcases p15191_3 (m.d 0 1) (by simp) with h15220 | h15220
                                  · linarith only [h11282, h15220, hlam]
                                  · rcases p15191_3 (m.d 0 2) (by simp) with h15222 | h15222
                                    · linarith only [h14874, h15222, hlam]
                                    · linarith only [h0, h15222, hlam]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h11844, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15191_1, u0elo4]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  rcases p15191_3 (m.d 0 1) (by simp) with h15226 | h15226
                                  · linarith only [h11282, h15226, hlam]
                                  · rcases p15191_3 (m.d 0 2) (by simp) with h15228 | h15228
                                    · linarith only [h14874, h15228, hlam]
                                    · linarith only [h11844, h15228, hlam]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [h15096, hlam, p15191_1]
                                · have p15191_0 := h15191c.1
                                  have p15191_1 := h15191c.2.1
                                  have p15191_2 := h15191c.2.2.1
                                  have p15191_3 := h15191c.2.2.2
                                  linarith only [hlam, p15191_0]
                              · linarith only [h11844, h11845, h15185, h15190, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h15096, h15097, h15098, h15189, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h15096, h15184, h9935, hlam]
            · linarith only [h11844, h11845, h15097, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h15237 | h15237
            · rcases m.htr 1 2 4 (by decide) (by decide) with h15238 | h15238
              · rcases m.htr 1 2 5 (by decide) (by decide) with h15239 | h15239
                · rcases m.htr 1 3 4 (by decide) (by decide) with h15240 | h15240
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h15241 | h15241
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h15242 | h15242
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h15243 | h15243
                        · linarith only [h11844, h11845, h15092, h15096, h15237, h15240, h15242, h15243, h6310, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15245 | h15245
                          · linarith only [h11844, h11845, h15094, h15096, h15237, h15240, h15242, h15245, h6310, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h15247 | h15247
                            · linarith only [h11844, h11845, h15096, h15237, h15240, h15243, h15247, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h11844, h11845, h15247, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h11844, h11845, h15238, h15242, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h15092, h15240, h15241, h6310, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h15252 | h15252
                    · linarith only [h15094, h15240, h15252, h6310, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h15254 | h15254
                      · linarith only [h11844, h11845, h15096, h15240, h15254, hc23, hc34, hlam, hphi]
                      · linarith only [h11844, h11845, h15238, h15254, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h11844, h11845, h15238, h15239, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h15258 | h15258
                · linarith only [h11844, h14874, h15238, h15258, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h15260 | h15260
                  · linarith only [h15092, h15237, h15238, h15260, h6310, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h15262 | h15262
                    · linarith only [h15094, h15260, h15262, h6310, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h15264 | h15264
                      · linarith only [h11844, h11845, h15096, h15260, h15264, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h15266 | h15266
                        · linarith only [h0, h11844, h15238, h15264, h15266, hc34, hc45, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15268 | h15268
                          · linarith only [h11282, h11844, h15237, h15238, h15262, h15264, h15268, h6310, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h15270 | h15270
                            · linarith only [h0, h11844, h15238, h15264, h15266, h15270, hc23, hc34, hlam, hphi]
                            · linarith only [h11844, h11845, h15270, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h11844, h11845, h15237, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 10516000 in
set_option maxHeartbeats 10516000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11844 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s17 m hb0 hb1 hb3 hb4 h0 h6310 h9935 h11282 h11844

end R2N4
