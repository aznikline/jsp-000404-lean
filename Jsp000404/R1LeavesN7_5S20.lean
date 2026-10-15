import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11852 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11853 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11854 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h11855 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h11856 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h12338 | h12338
  · linarith only [h11844, h11847, h11856, h12338, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h12340 | h12340
    · rcases m.htr 3 4 5 (by decide) (by decide) with h12341 | h12341
      · rcases h0bigk with h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c | h12342c
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [hlam, p12342_0]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h0, hlam, p12342_1]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h6310, hlam, p12342_0]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h9935, hlam, p12342_1]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11282, hlam, p12342_1]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          rcases p12342_3 (m.d 0 1) (by simp) with h12348 | h12348
          · linarith only [h0, h12348, hlam]
          · rcases p12342_3 (m.d 0 2) (by simp) with h12350 | h12350
            · rcases p12342_3 (m.d 0 3) (by simp) with h12351 | h12351
              · linarith only [h11844, h12351, hlam]
              · linarith only [h12351, h6310, hlam]
            · linarith only [h0, h12350, hlam]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [hlam, p12342_0]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11847, h12338, h12341, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12342_1, u0elo1]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11847, h12338, h12341, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12342_1, u0elo1]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11848, h12338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12342_1, u0elo1]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          rcases p12342_3 (m.d 0 1) (by simp) with h12359 | h12359
          · linarith only [h12359, h6310, hlam]
          · rcases p12342_3 (m.d 0 2) (by simp) with h12361 | h12361
            · rcases p12342_3 (m.d 0 3) (by simp) with h12362 | h12362
              · rcases p12342_3 (m.d 0 4) (by simp) with h12363 | h12363
                · linarith only [h11847, h12363, hlam]
                · linarith only [h12363, h9935, hlam]
              · linarith only [h12362, h6310, hlam]
            · linarith only [h0, h12361, hlam]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11844, hlam, p12342_1]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [hlam, p12342_0]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11847, h12338, h12341, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12342_1, u0elo2]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11844, h11848, h12338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12342_1, u0elo1]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          rcases p12342_3 (m.d 0 1) (by simp) with h12372 | h12372
          · linarith only [h12372, h9935, hlam]
          · rcases p12342_3 (m.d 0 2) (by simp) with h12374 | h12374
            · rcases p12342_3 (m.d 0 3) (by simp) with h12375 | h12375
              · rcases p12342_3 (m.d 0 4) (by simp) with h12376 | h12376
                · rcases p12342_3 (m.d 0 5) (by simp) with h12377 | h12377
                  · linarith only [h11849, h12377, hlam]
                  · linarith only [h11282, h12377, hlam]
                · linarith only [h12376, h9935, hlam]
              · linarith only [h12375, h6310, hlam]
            · linarith only [h0, h12374, hlam]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11845, hlam, p12342_0]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11847, hlam, p12342_0]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [hlam, p12342_0]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11848, h12338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12342_1, u0elo3]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          rcases p12342_3 (m.d 0 1) (by simp) with h12387 | h12387
          · linarith only [h11282, h12387, hlam]
          · rcases p12342_3 (m.d 0 2) (by simp) with h12389 | h12389
            · rcases p12342_3 (m.d 0 3) (by simp) with h12390 | h12390
              · rcases p12342_3 (m.d 0 4) (by simp) with h12391 | h12391
                · rcases p12342_3 (m.d 0 5) (by simp) with h12392 | h12392
                  · rcases h0emin with h12393 | h12393 | h12393 | h12393 | h12393
                    · linarith only [h12393, hlam, p12342_1, u0elo4]
                    · rcases h1bigk with h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c | h12395c
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h0, hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h6310, hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h9935, hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h11282, hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        rcases p12395_3 (m.d 0 1) (by simp) with h12401 | h12401
                        · linarith only [h12401, hlam, p12395_0]
                        · rcases p12395_3 (m.d 1 2) (by simp) with h12403 | h12403
                          · rcases p12395_3 (m.d 1 3) (by simp) with h12404 | h12404
                            · linarith only [h11850, h12404, hlam]
                            · linarith only [h12404, h6310, hlam]
                          · linarith only [h12403, hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h6310, hc01, hc12, hlam, hphi, p12395_1]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h9935, hc01, hc12, hlam, hphi, p12395_1]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h11282, hc01, hc12, hlam, hphi, p12395_1]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        rcases p12395_3 (m.d 0 1) (by simp) with h12412 | h12412
                        · linarith only [h12412, hlam, p12395_0]
                        · rcases p12395_3 (m.d 1 2) (by simp) with h12414 | h12414
                          · rcases p12395_3 (m.d 1 3) (by simp) with h12415 | h12415
                            · rcases p12395_3 (m.d 1 4) (by simp) with h12416 | h12416
                              · linarith only [h11853, h12416, hlam]
                              · linarith only [h12416, h9935, hlam]
                            · linarith only [h12415, hlam, p12395_0]
                          · linarith only [h0, h12414, hlam]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h11850, hlam, p12395_1]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h9935, hc01, hc13, hlam, hphi, p12395_1]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h11282, h11850, hc01, hc12, hlam, hphi, p12342_1, p12395_1]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        rcases p12395_3 (m.d 0 1) (by simp) with h12425 | h12425
                        · linarith only [h12425, hlam, p12395_0]
                        · rcases p12395_3 (m.d 1 2) (by simp) with h12427 | h12427
                          · rcases p12395_3 (m.d 1 3) (by simp) with h12428 | h12428
                            · rcases p12395_3 (m.d 1 4) (by simp) with h12429 | h12429
                              · rcases p12395_3 (m.d 1 5) (by simp) with h12430 | h12430
                                · linarith only [h11855, h12430, hlam]
                                · linarith only [h11282, h12430, hlam]
                              · linarith only [h12429, hlam, p12395_0]
                            · linarith only [h12428, h6310, hlam]
                          · linarith only [h0, h12427, hlam]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h11851, hlam, p12395_1]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h11853, hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h11282, hc01, hc14, hlam, hphi, p12342_1, p12395_1]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        rcases p12395_3 (m.d 0 1) (by simp) with h12440 | h12440
                        · linarith only [h12440, hlam, p12395_0]
                        · rcases p12395_3 (m.d 1 2) (by simp) with h12442 | h12442
                          · rcases p12395_3 (m.d 1 3) (by simp) with h12443 | h12443
                            · rcases p12395_3 (m.d 1 4) (by simp) with h12444 | h12444
                              · rcases p12395_3 (m.d 1 5) (by simp) with h12445 | h12445
                                · rcases h3bigk with h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h6310, hlam, p12446_1]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    rcases p12446_3 (m.d 0 3) (by simp) with h12449 | h12449
                                    · rcases p12446_3 (m.d 1 3) (by simp) with h12450 | h12450
                                      · rcases p12446_3 (m.d 2 3) (by simp) with h12451 | h12451
                                        · linarith only [h11844, h12451, hlam]
                                        · rcases p12446_3 (m.d 3 4) (by simp) with h12453 | h12453
                                          · linarith only [h11847, h12453, hlam]
                                          · linarith only [h11856, h12453, hlam]
                                      · linarith only [h11850, h12450, hlam]
                                    · linarith only [h11844, h12449, hlam]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11844, h12338, h12341, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12446_1, u0elo1]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11844, h12338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12446_1, u0elo1]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11847, h11850, h12338, h12341, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12446_1]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    rcases p12446_3 (m.d 0 3) (by simp) with h12462 | h12462
                                    · linarith only [h12462, h6310, hlam]
                                    · linarith only [h11844, h12462, hlam]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    rcases p12446_3 (m.d 0 3) (by simp) with h12465 | h12465
                                    · linarith only [h12465, h6310, hlam]
                                    · linarith only [h11847, h12465, hlam]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    rcases p12446_3 (m.d 0 3) (by simp) with h12468 | h12468
                                    · linarith only [h12468, h6310, hlam]
                                    · linarith only [h11848, h12468, hlam]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11844, hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11850, hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11856, hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h12338, hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11847, hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11853, hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11844, h11847, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12446_1, u0elo1]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11844, h11847, h12338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12446_1, u0elo1]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11848, hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11854, hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h11844, h11848, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12446_1, u0elo1]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [h12341, hlam, p12446_0]
                                  · have p12446_0 := h12446c.1
                                    have p12446_1 := h12446c.2.1
                                    have p12446_2 := h12446c.2.2.1
                                    have p12446_3 := h12446c.2.2.2
                                    linarith only [hlam, p12446_0]
                                · linarith only [h12445, hlam, p12395_0]
                              · linarith only [h12444, h9935, hlam]
                            · linarith only [h12443, h6310, hlam]
                          · linarith only [h0, h12442, hlam]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h11852, hlam, p12395_1]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h11854, hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [h11855, hlam, p12395_0]
                      · have p12395_0 := h12395c.1
                        have p12395_1 := h12395c.2.1
                        have p12395_2 := h12395c.2.2.1
                        have p12395_3 := h12395c.2.2.2
                        linarith only [hlam, p12395_0]
                    · rcases h1bigk with h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c | h12494c
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h0, hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h6310, hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h9935, hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h11282, hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        rcases p12494_3 (m.d 0 1) (by simp) with h12500 | h12500
                        · linarith only [h12500, hlam, p12494_0]
                        · rcases p12494_3 (m.d 1 2) (by simp) with h12502 | h12502
                          · rcases p12494_3 (m.d 1 3) (by simp) with h12503 | h12503
                            · linarith only [h11850, h12503, hlam]
                            · linarith only [h12503, h6310, hlam]
                          · linarith only [h12502, hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h6310, hc01, hc12, hlam, hphi, p12494_1]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h9935, hc01, hc12, hlam, hphi, p12494_1]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h11282, hc01, hc12, hlam, hphi, p12342_1, p12494_1]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        rcases p12494_3 (m.d 0 1) (by simp) with h12511 | h12511
                        · linarith only [h12511, hlam, p12494_0]
                        · rcases p12494_3 (m.d 1 2) (by simp) with h12513 | h12513
                          · rcases p12494_3 (m.d 1 3) (by simp) with h12514 | h12514
                            · rcases p12494_3 (m.d 1 4) (by simp) with h12515 | h12515
                              · linarith only [h11853, h12515, hlam]
                              · linarith only [h12515, h9935, hlam]
                            · linarith only [h12514, hlam, p12494_0]
                          · linarith only [h0, h12513, hlam]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h11850, hlam, p12494_1]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h11849, h9935, hc01, hc13, hlam, hphi, p12342_1, p12494_1]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h11282, h11850, hc01, hc12, hlam, hphi, p12342_1, p12494_1]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        rcases p12494_3 (m.d 0 1) (by simp) with h12524 | h12524
                        · linarith only [h12524, hlam, p12494_0]
                        · rcases p12494_3 (m.d 1 2) (by simp) with h12526 | h12526
                          · rcases p12494_3 (m.d 1 3) (by simp) with h12527 | h12527
                            · rcases p12494_3 (m.d 1 4) (by simp) with h12528 | h12528
                              · rcases p12494_3 (m.d 1 5) (by simp) with h12529 | h12529
                                · linarith only [h11855, h12529, hlam]
                                · linarith only [h11282, h12529, hlam]
                              · linarith only [h12528, hlam, p12494_0]
                            · linarith only [h12527, h6310, hlam]
                          · linarith only [h0, h12526, hlam]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h11851, hlam, p12494_1]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h11853, hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h11282, hc01, hc14, hlam, hphi, p12342_1, p12494_1]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        rcases p12494_3 (m.d 0 1) (by simp) with h12539 | h12539
                        · linarith only [h12539, hlam, p12494_0]
                        · rcases p12494_3 (m.d 1 2) (by simp) with h12541 | h12541
                          · rcases p12494_3 (m.d 1 3) (by simp) with h12542 | h12542
                            · rcases p12494_3 (m.d 1 4) (by simp) with h12543 | h12543
                              · rcases p12494_3 (m.d 1 5) (by simp) with h12544 | h12544
                                · rcases h3bigk with h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c | h12545c
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h6310, hlam, p12545_1]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    rcases p12545_3 (m.d 0 3) (by simp) with h12548 | h12548
                                    · rcases p12545_3 (m.d 1 3) (by simp) with h12549 | h12549
                                      · rcases p12545_3 (m.d 2 3) (by simp) with h12550 | h12550
                                        · linarith only [h11844, h12550, hlam]
                                        · rcases p12545_3 (m.d 3 4) (by simp) with h12552 | h12552
                                          · linarith only [h11847, h12552, hlam]
                                          · linarith only [h11856, h12552, hlam]
                                      · linarith only [h11850, h12549, hlam]
                                    · linarith only [h11844, h12548, hlam]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11844, h11856, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12545_1, u0elo1]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11844, h12338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12545_1, u0elo1]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11847, h11849, h11850, hc01, hc12, hlam, hphi, p12342_1, p12545_1]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    rcases p12545_3 (m.d 0 3) (by simp) with h12561 | h12561
                                    · linarith only [h12561, h6310, hlam]
                                    · linarith only [h11844, h12561, hlam]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    rcases p12545_3 (m.d 0 3) (by simp) with h12564 | h12564
                                    · linarith only [h12564, h6310, hlam]
                                    · linarith only [h11847, h12564, hlam]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    rcases p12545_3 (m.d 0 3) (by simp) with h12567 | h12567
                                    · linarith only [h12567, h6310, hlam]
                                    · linarith only [h11848, h12567, hlam]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11844, hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11850, hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11856, hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h12338, hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11847, hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11853, hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11844, h11847, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12545_1, u0elo1]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11844, h11847, h12338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12545_1, u0elo1]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11848, hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11854, hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h11844, h11848, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12545_1, u0elo1]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [h12341, hlam, p12545_0]
                                  · have p12545_0 := h12545c.1
                                    have p12545_1 := h12545c.2.1
                                    have p12545_2 := h12545c.2.2.1
                                    have p12545_3 := h12545c.2.2.2
                                    linarith only [hlam, p12545_0]
                                · linarith only [h12544, hlam, p12494_0]
                              · linarith only [h12543, h9935, hlam]
                            · linarith only [h12542, h6310, hlam]
                          · linarith only [h0, h12541, hlam]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h11852, hlam, p12494_1]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h11854, hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [h11855, hlam, p12494_0]
                      · have p12494_0 := h12494c.1
                        have p12494_1 := h12494c.2.1
                        have p12494_2 := h12494c.2.2.1
                        have p12494_3 := h12494c.2.2.2
                        linarith only [hlam, p12494_0]
                    · rcases h1bigk with h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c | h12593c
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h0, hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h6310, hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h9935, hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h11282, hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        rcases p12593_3 (m.d 0 1) (by simp) with h12599 | h12599
                        · linarith only [h12599, hlam, p12593_0]
                        · rcases p12593_3 (m.d 1 2) (by simp) with h12601 | h12601
                          · rcases p12593_3 (m.d 1 3) (by simp) with h12602 | h12602
                            · linarith only [h11850, h12602, hlam]
                            · linarith only [h12602, h6310, hlam]
                          · linarith only [h12601, hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h6310, hc01, hc12, hlam, hphi, p12593_1]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h9935, hc01, hc12, hlam, hphi, p12593_1]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h11282, hc01, hc12, hlam, hphi, p12342_1, p12593_1]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        rcases p12593_3 (m.d 0 1) (by simp) with h12610 | h12610
                        · linarith only [h12610, hlam, p12593_0]
                        · rcases p12593_3 (m.d 1 2) (by simp) with h12612 | h12612
                          · rcases p12593_3 (m.d 1 3) (by simp) with h12613 | h12613
                            · rcases p12593_3 (m.d 1 4) (by simp) with h12614 | h12614
                              · linarith only [h11853, h12614, hlam]
                              · linarith only [h12614, h9935, hlam]
                            · linarith only [h12613, hlam, p12593_0]
                          · linarith only [h0, h12612, hlam]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h11850, hlam, p12593_1]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h11849, h9935, hc01, hc13, hlam, hphi, p12342_1, p12593_1]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h11282, h11850, hc01, hc12, hlam, hphi, p12342_1, p12593_1]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        rcases p12593_3 (m.d 0 1) (by simp) with h12623 | h12623
                        · linarith only [h12623, hlam, p12593_0]
                        · rcases p12593_3 (m.d 1 2) (by simp) with h12625 | h12625
                          · rcases p12593_3 (m.d 1 3) (by simp) with h12626 | h12626
                            · rcases p12593_3 (m.d 1 4) (by simp) with h12627 | h12627
                              · rcases p12593_3 (m.d 1 5) (by simp) with h12628 | h12628
                                · linarith only [h11855, h12628, hlam]
                                · linarith only [h11282, h12628, hlam]
                              · linarith only [h12627, hlam, p12593_0]
                            · linarith only [h12626, h6310, hlam]
                          · linarith only [h0, h12625, hlam]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h11851, hlam, p12593_1]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h11853, hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h11282, hc01, hc14, hlam, hphi, p12342_1, p12593_1]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        rcases p12593_3 (m.d 0 1) (by simp) with h12638 | h12638
                        · linarith only [h12638, hlam, p12593_0]
                        · rcases p12593_3 (m.d 1 2) (by simp) with h12640 | h12640
                          · rcases p12593_3 (m.d 1 3) (by simp) with h12641 | h12641
                            · rcases p12593_3 (m.d 1 4) (by simp) with h12642 | h12642
                              · rcases p12593_3 (m.d 1 5) (by simp) with h12643 | h12643
                                · rcases h3bigk with h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c | h12644c
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h6310, hlam, p12644_1]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    rcases p12644_3 (m.d 0 3) (by simp) with h12647 | h12647
                                    · rcases p12644_3 (m.d 1 3) (by simp) with h12648 | h12648
                                      · rcases p12644_3 (m.d 2 3) (by simp) with h12649 | h12649
                                        · linarith only [h11844, h12649, hlam]
                                        · rcases p12644_3 (m.d 3 4) (by simp) with h12651 | h12651
                                          · linarith only [h11847, h12651, hlam]
                                          · linarith only [h11856, h12651, hlam]
                                      · linarith only [h11850, h12648, hlam]
                                    · linarith only [h11844, h12647, hlam]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11844, h11856, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12644_1, u0elo1]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11844, h12338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12644_1, u0elo1]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11847, h11849, h11850, hc01, hc12, hlam, hphi, p12342_1, p12644_1]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    rcases p12644_3 (m.d 0 3) (by simp) with h12660 | h12660
                                    · linarith only [h12660, h6310, hlam]
                                    · linarith only [h11844, h12660, hlam]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    rcases p12644_3 (m.d 0 3) (by simp) with h12663 | h12663
                                    · linarith only [h12663, h6310, hlam]
                                    · linarith only [h11847, h12663, hlam]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    rcases p12644_3 (m.d 0 3) (by simp) with h12666 | h12666
                                    · linarith only [h12666, h6310, hlam]
                                    · linarith only [h11848, h12666, hlam]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11844, hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11850, hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11856, hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h12338, hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11847, hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11853, hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11844, h11847, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12644_1, u0elo1]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11844, h11847, h12338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12644_1, u0elo1]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11848, hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11854, hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h11844, h11848, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12644_1, u0elo1]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [h12341, hlam, p12644_0]
                                  · have p12644_0 := h12644c.1
                                    have p12644_1 := h12644c.2.1
                                    have p12644_2 := h12644c.2.2.1
                                    have p12644_3 := h12644c.2.2.2
                                    linarith only [hlam, p12644_0]
                                · linarith only [h12643, hlam, p12593_0]
                              · linarith only [h12642, h9935, hlam]
                            · linarith only [h12641, h6310, hlam]
                          · linarith only [h0, h12640, hlam]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h11852, hlam, p12593_1]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h11854, hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [h11855, hlam, p12593_0]
                      · have p12593_0 := h12593c.1
                        have p12593_1 := h12593c.2.1
                        have p12593_2 := h12593c.2.2.1
                        have p12593_3 := h12593c.2.2.2
                        linarith only [hlam, p12593_0]
                    · rcases h1bigk with h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c | h12692c
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h0, hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h6310, hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h9935, hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h11282, hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        rcases p12692_3 (m.d 0 1) (by simp) with h12698 | h12698
                        · linarith only [h12698, hlam, p12692_0]
                        · rcases p12692_3 (m.d 1 2) (by simp) with h12700 | h12700
                          · rcases p12692_3 (m.d 1 3) (by simp) with h12701 | h12701
                            · linarith only [h11850, h12701, hlam]
                            · linarith only [h12701, h6310, hlam]
                          · linarith only [h12700, hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h6310, hc01, hc12, hlam, hphi, p12692_1]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h9935, hc01, hc12, hlam, hphi, p12692_1]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h11282, hc01, hc12, hlam, hphi, p12342_1, p12692_1]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        rcases p12692_3 (m.d 0 1) (by simp) with h12709 | h12709
                        · linarith only [h12709, hlam, p12692_0]
                        · rcases p12692_3 (m.d 1 2) (by simp) with h12711 | h12711
                          · rcases p12692_3 (m.d 1 3) (by simp) with h12712 | h12712
                            · rcases p12692_3 (m.d 1 4) (by simp) with h12713 | h12713
                              · linarith only [h11853, h12713, hlam]
                              · linarith only [h12713, h9935, hlam]
                            · linarith only [h12712, hlam, p12692_0]
                          · linarith only [h0, h12711, hlam]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h11850, hlam, p12692_1]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h11849, h9935, hc01, hc13, hlam, hphi, p12342_1, p12692_1]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h11282, h11850, hc01, hc12, hlam, hphi, p12342_1, p12692_1]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        rcases p12692_3 (m.d 0 1) (by simp) with h12722 | h12722
                        · linarith only [h12722, hlam, p12692_0]
                        · rcases p12692_3 (m.d 1 2) (by simp) with h12724 | h12724
                          · rcases p12692_3 (m.d 1 3) (by simp) with h12725 | h12725
                            · rcases p12692_3 (m.d 1 4) (by simp) with h12726 | h12726
                              · rcases p12692_3 (m.d 1 5) (by simp) with h12727 | h12727
                                · linarith only [h11855, h12727, hlam]
                                · linarith only [h11282, h12727, hlam]
                              · linarith only [h12726, hlam, p12692_0]
                            · linarith only [h12725, h6310, hlam]
                          · linarith only [h0, h12724, hlam]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h11851, hlam, p12692_1]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h11853, hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h11282, hc01, hc14, hlam, hphi, p12342_1, p12692_1]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        rcases p12692_3 (m.d 0 1) (by simp) with h12737 | h12737
                        · linarith only [h12737, hlam, p12692_0]
                        · rcases p12692_3 (m.d 1 2) (by simp) with h12739 | h12739
                          · rcases p12692_3 (m.d 1 3) (by simp) with h12740 | h12740
                            · rcases p12692_3 (m.d 1 4) (by simp) with h12741 | h12741
                              · rcases p12692_3 (m.d 1 5) (by simp) with h12742 | h12742
                                · rcases h3bigk with h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c | h12743c
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h6310, hlam, p12743_1]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    rcases p12743_3 (m.d 0 3) (by simp) with h12746 | h12746
                                    · rcases p12743_3 (m.d 1 3) (by simp) with h12747 | h12747
                                      · rcases p12743_3 (m.d 2 3) (by simp) with h12748 | h12748
                                        · linarith only [h11844, h12748, hlam]
                                        · rcases p12743_3 (m.d 3 4) (by simp) with h12750 | h12750
                                          · linarith only [h11847, h12750, hlam]
                                          · linarith only [h11856, h12750, hlam]
                                      · linarith only [h11850, h12747, hlam]
                                    · linarith only [h11844, h12746, hlam]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11844, h11856, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12743_1, u0elo1]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11844, h12338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12743_1, u0elo1]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11847, h11849, h11850, hc01, hc12, hlam, hphi, p12342_1, p12743_1]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    rcases p12743_3 (m.d 0 3) (by simp) with h12759 | h12759
                                    · linarith only [h12759, h6310, hlam]
                                    · linarith only [h11844, h12759, hlam]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    rcases p12743_3 (m.d 0 3) (by simp) with h12762 | h12762
                                    · linarith only [h12762, h6310, hlam]
                                    · linarith only [h11847, h12762, hlam]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    rcases p12743_3 (m.d 0 3) (by simp) with h12765 | h12765
                                    · linarith only [h12765, h6310, hlam]
                                    · linarith only [h11848, h12765, hlam]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11844, hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11850, hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11856, hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h12338, hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11847, hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11853, hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11844, h11847, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12743_1, u0elo1]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11844, h11847, h12338, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12743_1, u0elo1]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11848, hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11854, hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h11844, h11848, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12743_1, u0elo1]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [h12341, hlam, p12743_0]
                                  · have p12743_0 := h12743c.1
                                    have p12743_1 := h12743c.2.1
                                    have p12743_2 := h12743c.2.2.1
                                    have p12743_3 := h12743c.2.2.2
                                    linarith only [hlam, p12743_0]
                                · linarith only [h12742, hlam, p12692_0]
                              · linarith only [h12741, h9935, hlam]
                            · linarith only [h12740, h6310, hlam]
                          · linarith only [h0, h12739, hlam]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h11852, hlam, p12692_1]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h11854, hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [h11855, hlam, p12692_0]
                      · have p12692_0 := h12692c.1
                        have p12692_1 := h12692c.2.1
                        have p12692_2 := h12692c.2.2.1
                        have p12692_3 := h12692c.2.2.2
                        linarith only [hlam, p12692_0]
                  · linarith only [h11282, h12392, hlam]
                · linarith only [h12391, h9935, hlam]
              · linarith only [h12390, h6310, hlam]
            · linarith only [h0, h12389, hlam]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11846, hlam, p12342_1]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11848, hlam, p12342_0]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [h11849, hlam, p12342_1]
        · have p12342_0 := h12342c.1
          have p12342_1 := h12342c.2.1
          have p12342_2 := h12342c.2.2.1
          have p12342_3 := h12342c.2.2.2
          linarith only [hlam, p12342_0]
      · linarith only [h11844, h11847, h11849, h11856, h12341, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h12800 | h12800
      · linarith only [h11844, h11847, h12340, h12800, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
      · linarith only [h11844, h11847, h11849, h11856, h12800, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11852 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11853 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11854 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h11855 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h11856 | h11856
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851 h11852 h11853 h11854 h11855 h11856
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851 h11852 h11853 h11854 h11855 h11856

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11852 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11853 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11854 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h11855 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  linarith only [h11844, h11847, h11849, h11855, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11852 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11853 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11854 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  rcases m.htr 1 4 5 (by decide) (by decide) with h11855 | h11855
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851 h11852 h11853 h11854 h11855
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851 h11852 h11853 h11854 h11855

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11852 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11853 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11854 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  linarith only [h11844, h11848, h11854, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11852 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11853 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  rcases m.htr 1 3 5 (by decide) (by decide) with h11854 | h11854
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851 h11852 h11853 h11854
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851 h11852 h11853 h11854

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11852 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11853 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  linarith only [h11847, h11853, h6310, hlam]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11852 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  rcases m.htr 1 3 4 (by decide) (by decide) with h11853 | h11853
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851 h11852 h11853
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851 h11852 h11853

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11852 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  linarith only [h0, h11846, h11852, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h11852 | h11852
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851 h11852
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851 h11852

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  linarith only [h0, h11845, h11851, hlam]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h11851 | h11851
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850 h11851

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x1 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  linarith only [h0, h11844, h11850, hlam]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0 (m : N7Model)
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
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h11850 | h11850
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849 h11850

end R2N4
