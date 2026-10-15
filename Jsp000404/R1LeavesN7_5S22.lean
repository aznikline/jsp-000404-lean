import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S21

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x1 (m : N7Model)
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
    (h11847 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11848 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h13550 | h13550
  · linarith only [h11847, h11848, h13550, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h13552 | h13552
    · rcases m.htr 1 2 4 (by decide) (by decide) with h13553 | h13553
      · rcases m.htr 1 2 5 (by decide) (by decide) with h13554 | h13554
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13555 | h13555
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13556 | h13556
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13557 | h13557
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13558 | h13558
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13559 | h13559
                  · linarith only [h11844, h11848, h13559, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13561 | h13561
                    · linarith only [h11282, h11845, h11847, h11848, h13550, h13552, h13556, h13561, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13563 | h13563
                      · linarith only [h11844, h11848, h13550, h13552, h13556, h13558, h13563, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c | h13565c
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [hlam, p13565_0]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h0, hlam, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h6310, hlam, p13565_0]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h9935, hlam, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11282, hlam, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          rcases p13565_3 (m.d 0 1) (by simp) with h13571 | h13571
                          · linarith only [h0, h13571, hlam]
                          · rcases p13565_3 (m.d 0 2) (by simp) with h13573 | h13573
                            · rcases p13565_3 (m.d 0 3) (by simp) with h13574 | h13574
                              · linarith only [h11844, h13574, hlam]
                              · linarith only [h13574, h6310, hlam]
                            · linarith only [h0, h13573, hlam]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [hlam, p13565_0]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11847, hc34, hlam, hphi, ht0b, ht45, ht5b, p13565_1, u0elo1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          rcases p13565_3 (m.d 0 1) (by simp) with h13580 | h13580
                          · linarith only [h0, h13580, hlam]
                          · rcases p13565_3 (m.d 0 2) (by simp) with h13582 | h13582
                            · rcases p13565_3 (m.d 0 3) (by simp) with h13583 | h13583
                              · linarith only [h11844, h13583, hlam]
                              · linarith only [h11847, h13583, hlam]
                            · linarith only [h11845, h13582, hlam]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11844, h11848, h13558, hc34, hlam, hphi, ht0b, ht45, ht5b, p13565_1, u0elo1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11848, h13552, h13555, h13557, h13563, hc01, hc12, hlam, hphi, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11844, hlam, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [hlam, p13565_0]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11848, h13552, h13555, h13557, h13563, h9935, hc01, hc12, hlam, hphi, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11848, hlam, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11847, h11848, h13552, h13555, h13557, h13563, hc01, hc12, hlam, hphi, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11845, hlam, p13565_0]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11847, hlam, p13565_0]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [hlam, p13565_0]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h13550, hlam, p13565_0]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11848, h13552, h13555, h13557, h13563, hc01, hc12, hlam, hphi, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11846, hlam, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11844, h11848, h13552, h13555, h13557, h13558, h13563, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [h11848, h13552, h13555, h13557, h13563, h9935, hc01, hc12, hlam, hphi, p13565_1]
                        · have p13565_0 := h13565c.1
                          have p13565_1 := h13565c.2.1
                          have p13565_2 := h13565c.2.2.1
                          have p13565_3 := h13565c.2.2.2
                          linarith only [hlam, p13565_0]
                · linarith only [h11847, h11848, h13558, hc23, hc35, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13604 | h13604
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13605 | h13605
                  · linarith only [h11844, h11848, h13605, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13607 | h13607
                    · linarith only [h13557, h13607, h9935, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13609 | h13609
                      · linarith only [h11844, h11848, h13552, h13556, h13557, h13604, h13609, h9935, hc01, hc12, hlam, hphi]
                      · rcases h0bigk with h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c | h13611c
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [hlam, p13611_0]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h0, hlam, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h6310, hlam, p13611_0]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h9935, hlam, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11282, hlam, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          rcases p13611_3 (m.d 0 1) (by simp) with h13617 | h13617
                          · linarith only [h0, h13617, hlam]
                          · rcases p13611_3 (m.d 0 2) (by simp) with h13619 | h13619
                            · rcases p13611_3 (m.d 0 3) (by simp) with h13620 | h13620
                              · linarith only [h11844, h13620, hlam]
                              · linarith only [h13620, h6310, hlam]
                            · linarith only [h0, h13619, hlam]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [hlam, p13611_0]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11844, h13604, hc34, hlam, hphi, ht0b, ht45, ht5b, p13611_1, u0elo1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          rcases p13611_3 (m.d 0 1) (by simp) with h13626 | h13626
                          · linarith only [h0, h13626, hlam]
                          · rcases p13611_3 (m.d 0 2) (by simp) with h13628 | h13628
                            · rcases p13611_3 (m.d 0 3) (by simp) with h13629 | h13629
                              · linarith only [h11844, h13629, hlam]
                              · linarith only [h11847, h13629, hlam]
                            · linarith only [h11845, h13628, hlam]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11844, h11848, h13604, hc34, hlam, hphi, ht0b, ht45, ht5b, p13611_1, u0elo1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11848, h13552, h13556, hc01, hc12, hlam, hphi, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11844, hlam, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [hlam, p13611_0]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11848, h13552, h13556, h9935, hc01, hc12, hlam, hphi, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11848, hlam, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h13557, h9935, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11845, hlam, p13611_0]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11847, hlam, p13611_0]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [hlam, p13611_0]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h13550, hlam, p13611_0]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11848, h13552, h13556, hc01, hc12, hlam, hphi, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11846, hlam, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11848, h13552, h13556, h6310, hc01, hc12, hlam, hphi, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [h11848, h13552, h13556, h9935, hc01, hc12, hlam, hphi, p13611_1]
                        · have p13611_0 := h13611c.1
                          have p13611_1 := h13611c.2.1
                          have p13611_2 := h13611c.2.2.1
                          have p13611_3 := h13611c.2.2.2
                          linarith only [hlam, p13611_0]
                · linarith only [h11847, h11848, h13552, h13556, h13604, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13650 | h13650
              · linarith only [h13550, h13555, h13556, h13650, h9935, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13652 | h13652
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13653 | h13653
                  · linarith only [h13556, h13653, h6310, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13655 | h13655
                    · linarith only [h13650, h13655, h9935, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13657 | h13657
                      · linarith only [h13650, h13657, h9935, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases h0bigk with h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h0, hlam, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h6310, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h9935, hlam, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h11282, hlam, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          rcases p13659_3 (m.d 0 1) (by simp) with h13665 | h13665
                          · linarith only [h0, h13665, hlam]
                          · rcases p13659_3 (m.d 0 2) (by simp) with h13667 | h13667
                            · rcases p13659_3 (m.d 0 3) (by simp) with h13668 | h13668
                              · linarith only [h11844, h13668, hlam]
                              · linarith only [h13668, h6310, hlam]
                            · linarith only [h0, h13667, hlam]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h11844, h13652, hc34, hlam, hphi, ht0b, ht45, ht5b, p13659_1, u0elo1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          rcases p13659_3 (m.d 0 1) (by simp) with h13674 | h13674
                          · linarith only [h0, h13674, hlam]
                          · rcases p13659_3 (m.d 0 2) (by simp) with h13676 | h13676
                            · rcases p13659_3 (m.d 0 3) (by simp) with h13677 | h13677
                              · linarith only [h11844, h13677, hlam]
                              · linarith only [h11847, h13677, hlam]
                            · linarith only [h11845, h13676, hlam]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h11844, h11848, h13652, hc34, hlam, hphi, ht0b, ht45, ht5b, p13659_1, u0elo1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h13556, h6310, hc01, hc35, hlam, hphi, ht12, ht23, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h11844, hlam, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h13556, h13657, h6310, hc04, hc45, hlam, hphi, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h11848, hlam, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h11847, h13556, h13657, h6310, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h11845, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h11847, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h13550, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          rcases p13659_3 (m.d 0 1) (by simp) with h13692 | h13692
                          · linarith only [h11282, h13692, hlam]
                          · rcases p13659_3 (m.d 0 2) (by simp) with h13694 | h13694
                            · rcases p13659_3 (m.d 0 3) (by simp) with h13695 | h13695
                              · linarith only [h11848, h13695, hlam]
                              · linarith only [h13695, h6310, hlam]
                            · linarith only [h0, h13694, hlam]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h11846, hlam, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h11844, h13652, hc34, hlam, hphi, ht0b, ht45, ht5b, p13659_1, u0elo4]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          rcases p13659_3 (m.d 0 1) (by simp) with h13701 | h13701
                          · linarith only [h11282, h13701, hlam]
                          · rcases p13659_3 (m.d 0 2) (by simp) with h13703 | h13703
                            · rcases p13659_3 (m.d 0 3) (by simp) with h13704 | h13704
                              · linarith only [h11848, h13704, hlam]
                              · linarith only [h11847, h13704, hlam]
                            · linarith only [h11845, h13703, hlam]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [hlam, p13659_0]
                · linarith only [h11847, h13556, h13652, h6310, hc23, hc35, hlam, hphi]
          · linarith only [h11847, h13555, h6310, hlam]
        · linarith only [h0, h11846, h13554, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h11845, h13553, hlam]
    · linarith only [h0, h11844, h13552, hlam]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0 (m : N7Model)
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
    (h11847 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h11848 | h11848
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x1_x0 (m : N7Model)
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
    (h13714 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h13715 | h13715
  · rcases m.htr 1 2 3 (by decide) (by decide) with h13716 | h13716
    · rcases m.htr 1 2 4 (by decide) (by decide) with h13717 | h13717
      · rcases m.htr 1 2 5 (by decide) (by decide) with h13718 | h13718
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13719 | h13719
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13720 | h13720
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13721 | h13721
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13722 | h13722
                · linarith only [h11844, h11847, h13722, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13724 | h13724
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13725 | h13725
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13726 | h13726
                      · rcases h0bigk with h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c | h13727c
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [hlam, p13727_0]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h0, hlam, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h6310, hlam, p13727_0]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h9935, hlam, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11282, hlam, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          rcases p13727_3 (m.d 0 1) (by simp) with h13733 | h13733
                          · linarith only [h0, h13733, hlam]
                          · rcases p13727_3 (m.d 0 2) (by simp) with h13735 | h13735
                            · rcases p13727_3 (m.d 0 3) (by simp) with h13736 | h13736
                              · linarith only [h11844, h13736, hlam]
                              · linarith only [h13736, h6310, hlam]
                            · linarith only [h0, h13735, hlam]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [hlam, p13727_0]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11844, h13724, h13726, hc45, hlam, hphi, ht0b, ht5b, p13727_1, u0elo1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11844, h11847, h13724, h13726, hc45, hlam, hphi, ht0b, ht5b, p13727_1, u0elo1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          rcases p13727_3 (m.d 0 1) (by simp) with h13743 | h13743
                          · linarith only [h0, h13743, hlam]
                          · rcases p13727_3 (m.d 0 2) (by simp) with h13745 | h13745
                            · rcases p13727_3 (m.d 0 3) (by simp) with h13746 | h13746
                              · linarith only [h11844, h13746, hlam]
                              · linarith only [h13714, h13746, hlam]
                            · linarith only [h11846, h13745, hlam]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11847, h13716, h13719, hc01, hc12, hlam, hphi, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11844, hlam, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [hlam, p13727_0]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11847, hlam, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11847, h13716, h13719, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11847, h13716, h13719, hc01, hc12, hlam, hphi, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11845, hlam, p13727_0]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11844, h11847, h13716, h13719, h13724, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [hlam, p13727_0]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11282, h11847, h13716, h13719, hc01, hc12, hlam, hphi, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11847, h13714, h13716, h13719, hc01, hc12, hlam, hphi, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h11846, hlam, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h13714, hlam, p13727_0]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [h13715, hlam, p13727_1]
                        · have p13727_0 := h13727c.1
                          have p13727_1 := h13727c.2.1
                          have p13727_2 := h13727c.2.2.1
                          have p13727_3 := h13727c.2.2.2
                          linarith only [hlam, p13727_0]
                      · linarith only [h11845, h11847, h13715, h13726, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h11847, h13714, h13715, h13716, h13719, h13722, h13724, h13725, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h11847, h13714, h13716, h13719, h13724, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h11847, h13714, h13715, h13716, h13719, h13721, h9935, hc01, hc12, hlam, hphi]
            · linarith only [h11847, h13714, h13719, h13720, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13770 | h13770
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13771 | h13771
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13772 | h13772
                · linarith only [h13719, h13772, h6310, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13774 | h13774
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13775 | h13775
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13776 | h13776
                      · rcases h0bigk with h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c | h13777c
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [hlam, p13777_0]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h0, hlam, p13777_1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h6310, hlam, p13777_0]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h9935, hlam, p13777_1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h11282, hlam, p13777_1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          rcases p13777_3 (m.d 0 1) (by simp) with h13783 | h13783
                          · linarith only [h0, h13783, hlam]
                          · rcases p13777_3 (m.d 0 2) (by simp) with h13785 | h13785
                            · rcases p13777_3 (m.d 0 3) (by simp) with h13786 | h13786
                              · linarith only [h11844, h13786, hlam]
                              · linarith only [h13786, h6310, hlam]
                            · linarith only [h0, h13785, hlam]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [hlam, p13777_0]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h11844, h13774, h13776, hc45, hlam, hphi, ht0b, ht5b, p13777_1, u0elo1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h11845, h13772, h13774, h13776, hc45, hlam, hphi, ht0b, ht5b, p13777_1, u0elo1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          rcases p13777_3 (m.d 0 1) (by simp) with h13793 | h13793
                          · linarith only [h0, h13793, hlam]
                          · rcases p13777_3 (m.d 0 2) (by simp) with h13795 | h13795
                            · rcases p13777_3 (m.d 0 3) (by simp) with h13796 | h13796
                              · linarith only [h11844, h13796, hlam]
                              · linarith only [h13714, h13796, hlam]
                            · linarith only [h11846, h13795, hlam]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h13719, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p13777_1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h11844, hlam, p13777_1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [hlam, p13777_0]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h11847, hlam, p13777_1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h11282, h13719, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p13777_1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          rcases p13777_3 (m.d 0 1) (by simp) with h13805 | h13805
                          · linarith only [h13805, h9935, hlam]
                          · rcases p13777_3 (m.d 0 2) (by simp) with h13807 | h13807
                            · rcases p13777_3 (m.d 0 3) (by simp) with h13808 | h13808
                              · linarith only [h11847, h13808, hlam]
                              · linarith only [h13808, h6310, hlam]
                            · linarith only [h0, h13807, hlam]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h11845, hlam, p13777_0]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h11844, h13774, h13776, hc45, hlam, hphi, ht0b, ht5b, p13777_1, u0elo3]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [hlam, p13777_0]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          rcases p13777_3 (m.d 0 1) (by simp) with h13815 | h13815
                          · linarith only [h13815, h9935, hlam]
                          · rcases p13777_3 (m.d 0 2) (by simp) with h13817 | h13817
                            · rcases p13777_3 (m.d 0 3) (by simp) with h13818 | h13818
                              · linarith only [h11847, h13818, hlam]
                              · linarith only [h13714, h13818, hlam]
                            · linarith only [h11846, h13817, hlam]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h13714, h13719, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p13777_1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h11846, hlam, p13777_1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h13714, hlam, p13777_0]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [h13715, hlam, p13777_1]
                        · have p13777_0 := h13777c.1
                          have p13777_1 := h13777c.2.1
                          have p13777_2 := h13777c.2.2.1
                          have p13777_3 := h13777c.2.2.2
                          linarith only [hlam, p13777_0]
                      · linarith only [h13719, h13776, h6310, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h11845, h13715, h13772, h13774, h13775, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h13714, h13719, h13774, h6310, hc23, hc34, hlam, hphi]
              · linarith only [h13715, h13771, h9935, hlam]
            · linarith only [h13714, h13770, h6310, hlam]
        · linarith only [h0, h11846, h13718, hlam]
      · linarith only [h0, h11845, h13717, hlam]
    · linarith only [h0, h11844, h13716, hlam]
  · linarith only [h11847, h13714, h13715, hlam]

end R2N4
