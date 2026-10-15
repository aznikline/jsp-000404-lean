import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_24S14
import Jsp000404.R1LeavesN7_24S15
import Jsp000404.R1LeavesN7_24S16
import Jsp000404.R1LeavesN7_24S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12148000 in
set_option maxHeartbeats 12148000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3888 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4439 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4818 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h5094 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5645 | h5645
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5646 | h5646
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5647 | h5647
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5648 | h5648
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5649 | h5649
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5650 | h5650
            · linarith only [h5094, h5645, h5650, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5652 | h5652
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5653 | h5653
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5654 | h5654
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5655 | h5655
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5656 | h5656
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5657 | h5657
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5658 | h5658
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5659 | h5659
                            · rcases h0bigk with h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c | h5660c
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [hlam, p5660_0]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h0, hlam, p5660_1]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h3888, hlam, p5660_0]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h4439, hlam, p5660_1]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h4818, hlam, p5660_1]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h0, h5650, hc01, hc23, hlam, hphi, ht12, p5660_1]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [hlam, p5660_0]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h5094, hlam, p5660_0]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h0, h4439, h5650, hc01, hc23, hlam, hphi, ht12, p5660_1]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h0, h4818, h5650, hc01, hc23, hlam, hphi, ht12, p5660_1]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h3888, hc01, hlam, hphi, p5660_1, u1elo2]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h3888, h5645, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5660_1, u1elo2]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [hlam, p5660_0]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h3888, h5645, h5656, h5659, hc45, hlam, hphi, ht01, ht0b, ht5b, p5660_1, u1elo2]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h3888, h4818, hc01, hlam, hphi, p5660_1, u1elo2]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h4439, hc01, hlam, hphi, p5660_1, u1elo3]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h5645, hlam, p5660_0]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h5647, hlam, p5660_0]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [hlam, p5660_0]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h0, h4818, h5645, hc01, hlam, hphi, p5660_1, u1elo1]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h4818, hc01, hlam, hphi, p5660_1, u1elo4]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h5646, hlam, p5660_1]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h5648, hlam, p5660_0]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [h5649, hlam, p5660_1]
                              · have p5660_0 := h5660c.1
                                have p5660_1 := h5660c.2.1
                                have p5660_2 := h5660c.2.2.1
                                have p5660_3 := h5660c.2.2.2
                                linarith only [hlam, p5660_0]
                            · linarith only [h0, h5645, h5650, h5658, h5659, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5687 | h5687
                            · linarith only [h5656, h5658, h5687, hlam]
                            · rcases h0bigk with h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c | h5689c
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [hlam, p5689_0]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h0, hlam, p5689_1]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h3888, hlam, p5689_0]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h4439, hlam, p5689_1]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h4818, hlam, p5689_1]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h0, h5650, hc01, hc23, hlam, hphi, ht12, p5689_1]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [hlam, p5689_0]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h5094, hlam, p5689_0]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h0, h5649, h5650, h5656, h5658, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5689_1]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h0, h4818, h5650, hc01, hc23, hlam, hphi, ht12, p5689_1]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h3888, hc01, hlam, hphi, p5689_1, u1elo2]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5689_1, u1elo2]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [hlam, p5689_0]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h3888, h5649, h5656, h5658, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5689_1, u1elo2]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h3888, h4818, hc01, hlam, hphi, p5689_1, u1elo2]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h0, h5645, h5650, hc01, hc23, hlam, hphi, ht12, p5689_1]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h5645, hlam, p5689_0]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h5647, hlam, p5689_0]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [hlam, p5689_0]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h0, h4818, h5645, h5650, hc01, hc23, hlam, hphi, ht12, p5689_1]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h4818, h5650, h5652, h5655, hc01, hc23, hlam, hphi, ht12, p5689_1]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h5646, hlam, p5689_1]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h5648, hlam, p5689_0]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [h5649, hlam, p5689_1]
                              · have p5689_0 := h5689c.1
                                have p5689_1 := h5689c.2.1
                                have p5689_2 := h5689c.2.2.1
                                have p5689_3 := h5689c.2.2.2
                                linarith only [hlam, p5689_0]
                        · linarith only [h0, h3888, h5648, h5650, h5657, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · linarith only [h4818, h5650, h5652, h5655, h5656, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h4439, h5645, h5649, h5655, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h3888, h5648, h5654, hlam]
                · linarith only [h3888, h5647, h5653, hlam]
              · linarith only [h0, h5645, h5652, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5721 | h5721
            · linarith only [h5094, h5645, h5721, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5723 | h5723
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5724 | h5724
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5725 | h5725
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5726 | h5726
                    · linarith only [h4439, h5649, h5721, h5723, h5726, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5728 | h5728
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5729 | h5729
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5730 | h5730
                          · linarith only [h5645, h5726, h5730, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5732 | h5732
                            · linarith only [h4439, h5646, h5726, h5728, h5730, h5732, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases h0bigk with h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [hlam, p5734_0]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h0, hlam, p5734_1]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h3888, hlam, p5734_0]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h4439, hlam, p5734_1]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h4818, hlam, p5734_1]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h0, h5721, hc01, hc23, hlam, hphi, ht12, p5734_1]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [hlam, p5734_0]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h5094, hlam, p5734_0]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h0, h4439, h5721, hc01, hc23, hlam, hphi, ht12, p5734_1]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h0, h4818, h5721, hc01, hc23, hlam, hphi, ht12, p5734_1]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h3888, hc01, hlam, hphi, p5734_1, u1elo2]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h3888, h5646, hc25, hlam, hphi, ht01, ht0b, ht5b, p5734_1, u1elo2]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [hlam, p5734_0]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h3888, h4439, hc01, hlam, hphi, p5734_1, u1elo2]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h3888, h4818, hc01, hlam, hphi, p5734_1, u1elo2]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h4439, hc01, hlam, hphi, p5734_1, u1elo3]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h5645, hlam, p5734_0]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h5647, hlam, p5734_0]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [hlam, p5734_0]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h5649, hlam, p5734_0]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h4818, hc01, hlam, hphi, p5734_1, u1elo4]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h5646, hlam, p5734_1]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h5648, hlam, p5734_0]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [h0, h4439, h5646, h5721, hc01, hc23, hlam, hphi, ht12, p5734_1]
                              · have p5734_0 := h5734c.1
                                have p5734_1 := h5734c.2.1
                                have p5734_2 := h5734c.2.2.1
                                have p5734_3 := h5734c.2.2.2
                                linarith only [hlam, p5734_0]
                        · linarith only [h0, h5721, h5729, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h5721, h5728, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h3888, h5646, h5648, h5725, hc01, hlam, hphi, u1elo1]
                · linarith only [h3888, h4439, h5647, h5724, hc01, hlam, hphi, u1elo3]
              · linarith only [h0, h5645, h5723, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h5094, h5646, h5648, hlam]
      · linarith only [h5094, h5645, h5647, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5767 | h5767
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5768 | h5768
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5769 | h5769
          · linarith only [h5645, h5646, h5769, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5771 | h5771
            · linarith only [h5094, h5645, h5771, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5773 | h5773
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5774 | h5774
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5775 | h5775
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5776 | h5776
                    · linarith only [h4439, h5769, h5773, h5776, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5778 | h5778
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5779 | h5779
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5780 | h5780
                          · linarith only [h5645, h5776, h5780, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5782 | h5782
                            · linarith only [h4439, h5645, h5776, h5778, h5782, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases h0bigk with h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [hlam, p5784_0]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h0, hlam, p5784_1]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h3888, hlam, p5784_0]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h4439, hlam, p5784_1]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h4818, hlam, p5784_1]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h5646, h5780, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5784_1]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [hlam, p5784_0]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h5094, hlam, p5784_0]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h5646, h5780, hc04, hc45, hlam, hphi, p5784_1]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h5646, hlam, p5784_0]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h3888, hc01, hlam, hphi, p5784_1, u1elo2]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5784_1, u1elo2]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [hlam, p5784_0]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h3888, h4439, hc01, hlam, hphi, p5784_1, u1elo2]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h3888, h4818, hc01, hlam, hphi, p5784_1, u1elo2]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h4439, hc01, hlam, hphi, p5784_1, u1elo3]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h5645, hlam, p5784_0]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h5767, hlam, p5784_0]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [hlam, p5784_0]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h5769, hlam, p5784_0]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h4818, hc01, hlam, hphi, p5784_1, u1elo4]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h0, h4818, hc01, hlam, hphi, p5784_1, u1elo4]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h5768, hlam, p5784_0]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [h3888, h4439, h5768, hc01, hlam, hphi, p5784_1, u1elo2]
                              · have p5784_0 := h5784c.1
                                have p5784_1 := h5784c.2.1
                                have p5784_2 := h5784c.2.2.1
                                have p5784_3 := h5784c.2.2.2
                                linarith only [hlam, p5784_0]
                        · linarith only [h3888, h5768, h5771, h5779, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · linarith only [h4439, h5771, h5773, h5778, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3888, h5768, h5775, hlam]
                · linarith only [h3888, h4439, h5767, h5771, h5773, h5774, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h5645, h5773, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5815 | h5815
          · linarith only [h5645, h5646, h5815, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5817 | h5817
            · linarith only [h5094, h5645, h5817, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5819 | h5819
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5820 | h5820
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5821 | h5821
                  · linarith only [h5094, h5645, h5768, h5821, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5823 | h5823
                    · linarith only [h4439, h5815, h5819, h5823, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5825 | h5825
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5826 | h5826
                        · linarith only [h0, h5817, h5821, h5826, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h4439, h5817, h5819, h5826, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h4439, h5817, h5819, h5825, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h3888, h4439, h5767, h5819, h5820, hc01, hlam, hphi, u1elo1]
              · linarith only [h0, h5645, h5819, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h5094, h5645, h5767, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5833 | h5833
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5834 | h5834
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5835 | h5835
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5836 | h5836
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5837 | h5837
            · linarith only [h5094, h5833, h5837, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5839 | h5839
              · linarith only [h5645, h5833, h5837, h5839, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5841 | h5841
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5842 | h5842
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5843 | h5843
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5844 | h5844
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5845 | h5845
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5846 | h5846
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5847 | h5847
                            · rcases h0bigk with h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c | h5848c
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [hlam, p5848_0]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h0, hlam, p5848_1]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h3888, hlam, p5848_0]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h4439, hlam, p5848_1]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h4818, hlam, p5848_1]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h0, h5839, h5841, hc01, hlam, hphi, p5848_1, u1elo2]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [hlam, p5848_0]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h5094, hlam, p5848_0]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h5645, hlam, p5848_1]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h0, h4818, h5839, h5841, hc01, hlam, hphi, p5848_1, u1elo2]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h3888, hc01, hlam, hphi, p5848_1, u1elo2]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5848_1, u1elo2]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [hlam, p5848_0]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h3888, h4439, hc01, hlam, hphi, p5848_1, u1elo2]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h3888, h4818, hc01, hlam, hphi, p5848_1, u1elo2]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h4439, h5841, hc01, hlam, hphi, p5848_1, u1elo2]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h4439, h5833, h5841, h5845, h5847, hc45, hlam, hphi, ht01, ht0b, ht5b, p5848_1, u1elo2]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h5834, hlam, p5848_0]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [hlam, p5848_0]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h4439, h4818, h5841, hc01, hlam, hphi, p5848_1, u1elo2]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h4818, h5841, h5843, hc01, hlam, hphi, p5848_1, u1elo2]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h5833, hlam, p5848_1]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h5835, hlam, p5848_0]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [h5836, hlam, p5848_1]
                              · have p5848_0 := h5848c.1
                                have p5848_1 := h5848c.2.1
                                have p5848_2 := h5848c.2.2.1
                                have p5848_3 := h5848c.2.2.2
                                linarith only [hlam, p5848_0]
                            · rcases h0bigk with h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c | h5874c
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [hlam, p5874_0]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h0, hlam, p5874_1]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h3888, hlam, p5874_0]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h4439, hlam, p5874_1]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h4818, hlam, p5874_1]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h0, h5839, h5841, hc01, hlam, hphi, p5874_1, u1elo2]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [hlam, p5874_0]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h5094, hlam, p5874_0]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h5645, hlam, p5874_1]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h0, h4818, h5839, h5841, hc01, hlam, hphi, p5874_1, u1elo2]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h3888, hc01, hlam, hphi, p5874_1, u1elo2]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5874_1, u1elo2]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [hlam, p5874_0]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h3888, h4439, hc01, hlam, hphi, p5874_1, u1elo2]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h3888, h4818, hc01, hlam, hphi, p5874_1, u1elo2]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h4439, h5841, hc01, hlam, hphi, p5874_1, u1elo2]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h4439, h5833, h5841, hc25, hlam, hphi, ht01, ht0b, ht5b, p5874_1, u1elo2]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h5834, hlam, p5874_0]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [hlam, p5874_0]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h4439, h4818, h5841, hc01, hlam, hphi, p5874_1, u1elo2]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h4818, h5841, h5843, hc01, hlam, hphi, p5874_1, u1elo2]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h5833, hlam, p5874_1]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h5835, hlam, p5874_0]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [h5836, hlam, p5874_1]
                              · have p5874_0 := h5874c.1
                                have p5874_1 := h5874c.2.1
                                have p5874_2 := h5874c.2.2.1
                                have p5874_3 := h5874c.2.2.2
                                linarith only [hlam, p5874_0]
                          · linarith only [h0, h5839, h5846, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h5094, h5835, h5845, hlam]
                      · linarith only [h0, h5837, h5844, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h3888, h4439, h5834, h5836, h5843, hc01, hlam, hphi, u1elo2]
                  · linarith only [h0, h3888, h5833, h5835, h5842, hc01, hlam, hphi, u1elo1]
                · linarith only [h3888, h5834, h5841, hlam]
          · linarith only [h5645, h5833, h5836, hlam]
        · linarith only [h5645, h5833, h5834, h5835, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5908 | h5908
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5909 | h5909
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5910 | h5910
            · linarith only [h0, h5094, h5910, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5912 | h5912
              · linarith only [h4818, h5645, h5833, h5912, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5914 | h5914
                · linarith only [h4818, h5094, h5833, h5834, h5914, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5916 | h5916
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5917 | h5917
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5918 | h5918
                      · linarith only [h0, h5910, h5914, h5918, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h5910, h5918, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h5909, h5910, h5914, h5917, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h5908, h5910, h5916, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
          · linarith only [h5094, h5833, h5834, h5909, hlam]
        · linarith only [h5094, h5833, h5908, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5925 | h5925
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5926 | h5926
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5927 | h5927
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5928 | h5928
            · linarith only [h0, h5094, h5928, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5930 | h5930
              · linarith only [h0, h5645, h5928, h5930, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5932 | h5932
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5933 | h5933
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5934 | h5934
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5935 | h5935
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5936 | h5936
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5937 | h5937
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5938 | h5938
                            · rcases h0bigk with h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c | h5939c
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [hlam, p5939_0]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h0, hlam, p5939_1]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h3888, hlam, p5939_0]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h4439, hlam, p5939_1]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h4818, hlam, p5939_1]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h5833, hc01, hc25, hlam, hphi, ht12, p5939_1]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [hlam, p5939_0]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h5094, hlam, p5939_0]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h5645, hlam, p5939_1]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h5833, hlam, p5939_0]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h3888, hc01, hlam, hphi, p5939_1, u1elo2]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5939_1, u1elo2]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [hlam, p5939_0]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h3888, h4439, hc01, hlam, hphi, p5939_1, u1elo2]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h0, h3888, h5833, hc01, hlam, hphi, p5939_1, u1elo2]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h4439, h5932, hc01, hlam, hphi, p5939_1, u1elo2]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h0, h4439, h5932, hc01, hlam, hphi, p5939_1, u1elo2]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h5925, hlam, p5939_0]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [hlam, p5939_0]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h0, h4439, h5833, h5932, hc01, hlam, hphi, p5939_1, u1elo2]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h4818, hc01, hlam, hphi, p5939_1, u1elo4]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h0, h4818, hc01, hlam, hphi, p5939_1, u1elo4]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h5926, hlam, p5939_0]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [h5927, hlam, p5939_1]
                              · have p5939_0 := h5939c.1
                                have p5939_1 := h5939c.2.1
                                have p5939_2 := h5939c.2.2.1
                                have p5939_3 := h5939c.2.2.2
                                linarith only [hlam, p5939_0]
                            · rcases h0bigk with h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c | h5965c
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [hlam, p5965_0]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h0, hlam, p5965_1]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h3888, hlam, p5965_0]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h4439, hlam, p5965_1]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h4818, hlam, p5965_1]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h0, h5930, h5932, hc01, hlam, hphi, p5965_1, u1elo2]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [hlam, p5965_0]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h5094, hlam, p5965_0]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h5645, hlam, p5965_1]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h5833, hlam, p5965_0]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h3888, hc01, hlam, hphi, p5965_1, u1elo2]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h0, h3888, hc01, hlam, hphi, p5965_1, u1elo2]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [hlam, p5965_0]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h3888, h5927, h5938, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5965_1, u1elo2]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h3888, h4818, hc01, hlam, hphi, p5965_1, u1elo2]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h4439, h5932, hc01, hlam, hphi, p5965_1, u1elo2]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h0, h4439, h5932, hc01, hlam, hphi, p5965_1, u1elo2]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h5925, hlam, p5965_0]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [hlam, p5965_0]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h4439, h4818, h5932, hc01, hlam, hphi, p5965_1, u1elo2]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h4818, h5932, h5934, hc01, hlam, hphi, p5965_1, u1elo2]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h0, h4818, h5932, h5934, hc01, hlam, hphi, p5965_1, u1elo2]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h5926, hlam, p5965_0]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [h5927, hlam, p5965_1]
                              · have p5965_0 := h5965c.1
                                have p5965_1 := h5965c.2.1
                                have p5965_2 := h5965c.2.2.1
                                have p5965_3 := h5965c.2.2.2
                                linarith only [hlam, p5965_0]
                          · linarith only [h0, h5930, h5937, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h3888, h5094, h5926, h5936, hc01, hlam, hphi, u1elo2]
                      · linarith only [h0, h5928, h5935, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h4439, h5927, h5934, hlam]
                  · linarith only [h3888, h5926, h5933, hlam]
                · linarith only [h3888, h5925, h5932, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5997 | h5997
            · linarith only [h0, h5094, h5997, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5999 | h5999
              · linarith only [h0, h5645, h5997, h5999, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6001 | h6001
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6002 | h6002
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6003 | h6003
                    · linarith only [h4439, h5927, h6001, h6003, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6005 | h6005
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6006 | h6006
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6007 | h6007
                          · linarith only [h0, h5999, h6003, h6007, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h5999, h6007, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h3888, h5094, h5926, h6006, hc01, hlam, hphi, u1elo2]
                      · linarith only [h0, h5925, h5997, h6005, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h3888, h5926, h6002, hlam]
                · linarith only [h3888, h5925, h6001, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6014 | h6014
          · linarith only [h5925, h5926, h6014, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6016 | h6016
            · linarith only [h0, h5094, h6016, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6018 | h6018
              · linarith only [h0, h5645, h6016, h6018, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6020 | h6020
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6021 | h6021
                  · linarith only [h5925, h5926, h6021, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6023 | h6023
                    · linarith only [h4439, h6014, h6020, h6021, h6023, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6025 | h6025
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6026 | h6026
                        · linarith only [h0, h6018, h6020, h6021, h6026, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h6016, h6026, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h5925, h6016, h6025, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h3888, h4439, h5925, h6020, hc01, hlam, hphi, u1elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6031 | h6031
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6032 | h6032
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6033 | h6033
            · linarith only [h0, h5094, h6033, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6035 | h6035
              · linarith only [h0, h5645, h6035, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6037 | h6037
                · linarith only [h5925, h6031, h6037, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6039 | h6039
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6040 | h6040
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6041 | h6041
                      · linarith only [h0, h6033, h6037, h6041, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h6033, h6041, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h3888, h4439, h6031, h6032, h6040, hc01, hlam, hphi, u1elo2]
                  · linarith only [h3888, h6031, h6039, hlam]
          · linarith only [h5925, h6031, h6032, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6047 | h6047
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6048 | h6048
            · linarith only [h0, h5094, h6048, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6050 | h6050
              · linarith only [h0, h5645, h6050, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6052 | h6052
                · linarith only [h3888, h5925, h6052, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6054 | h6054
                  · linarith only [h6031, h6052, h6054, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6056 | h6056
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6057 | h6057
                      · linarith only [h3888, h6052, h6057, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h6048, h6057, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h4439, h6047, h6056, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6061 | h6061
            · linarith only [h0, h5094, h6061, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6063 | h6063
              · linarith only [h0, h5645, h6063, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6065 | h6065
                · linarith only [h0, h5094, h5925, h6065, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6067 | h6067
                  · linarith only [h0, h5094, h6031, h6065, h6067, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6069 | h6069
                    · linarith only [h4439, h6047, h6069, hc01, hlam, hphi, u1elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6071 | h6071
                      · linarith only [h0, h6061, h6065, h6071, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h6061, h6071, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 12148000 in
set_option maxHeartbeats 12148000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3888 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4439 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4818 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h5094 | h5094
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h3888 h4439 h4818 h5094
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h3888 h4439 h4818 h5094

set_option maxHeartbeats 12148000 in
set_option maxHeartbeats 12148000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3888 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4439 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h4818 | h4818
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h3888 h4439 h4818
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h3888 h4439 h4818

set_option maxHeartbeats 12148000 in
set_option maxHeartbeats 12148000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3888 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h4439 | h4439
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h3888 h4439
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h3888 h4439

set_option maxHeartbeats 12148000 in
set_option maxHeartbeats 12148000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h3888 | h3888
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x0 m hb0 hb1 hb3 hb4 h0 h3888
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1 m hb0 hb1 hb3 hb4 h0 h3888

set_option maxHeartbeats 12148000 in
set_option maxHeartbeats 12148000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
