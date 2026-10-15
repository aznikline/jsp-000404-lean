import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5416000 in
set_option maxHeartbeats 5416000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s4_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3095 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3633 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3927 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4554 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h4555 | h4555
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4556 | h4556
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4557 | h4557
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4558 | h4558
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4559 | h4559
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4560 | h4560
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4561 | h4561
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4562 | h4562
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4563 | h4563
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4564 | h4564
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4565 | h4565
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4566 | h4566
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4567 | h4567
                          · rcases h0bigk with h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [hlam, p4568_0]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h0, hlam, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h3095, hlam, p4568_0]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h3633, hlam, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h3927, hlam, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [hlam, p4568_0]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h0, h4553, h4564, h4567, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h0, h4554, h4564, h4567, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h0, h3927, hc01, hc12, hlam, hphi, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h3095, hc01, hc13, hlam, hphi, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h4553, hlam, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [hlam, p4568_0]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h0, h4553, h4554, h4564, h4567, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h0, h3927, h4553, hc01, hc12, hlam, hphi, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h3633, hc01, hc14, hlam, hphi, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h4554, hlam, p4568_0]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h4556, hlam, p4568_0]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [hlam, p4568_0]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h0, h3927, h4553, h4556, hc01, hc12, hlam, hphi, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4568_1, u5elo0]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h4555, hlam, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h4557, hlam, p4568_0]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [h4558, hlam, p4568_1]
                            · have p4568_0 := h4568c.1
                              have p4568_1 := h4568c.2.1
                              have p4568_2 := h4568c.2.2.1
                              have p4568_3 := h4568c.2.2.2
                              linarith only [hlam, p4568_0]
                          · rcases h0bigk with h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c | h4594c
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [hlam, p4594_0]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h0, hlam, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h3095, hlam, p4594_0]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h3633, hlam, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h3927, hlam, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [hlam, p4594_0]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h0, h3095, hc01, hc12, hlam, hphi, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h0, h3633, hc01, hc12, hlam, hphi, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h0, h3927, hc01, hc12, hlam, hphi, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h3095, h4559, hc01, hc12, hlam, hphi, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h4553, hlam, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [hlam, p4594_0]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h3095, h3633, h4559, hc01, hc12, hlam, hphi, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h3095, h3927, h4559, hc01, hc12, hlam, hphi, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h3633, h4559, h4562, hc01, hc12, hlam, hphi, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h4554, hlam, p4594_0]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h4556, hlam, p4594_0]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [hlam, p4594_0]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h3633, h3927, h4559, h4562, hc01, hc12, hlam, hphi, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4594_1, u5elo0]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h4555, hlam, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h4557, hlam, p4594_0]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [h4558, hlam, p4594_1]
                            · have p4594_0 := h4594c.1
                              have p4594_1 := h4594c.2.1
                              have p4594_2 := h4594c.2.2.1
                              have p4594_3 := h4594c.2.2.2
                              linarith only [hlam, p4594_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4620 | h4620
                          · linarith only [h0, h4553, h4564, h4566, h4620, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases h0bigk with h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c | h4622c
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [hlam, p4622_0]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h0, hlam, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h3095, hlam, p4622_0]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h3633, hlam, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h3927, hlam, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [hlam, p4622_0]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h0, h3095, hc01, hc12, hlam, hphi, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h0, h3633, hc01, hc12, hlam, hphi, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h0, h3927, hc01, hc12, hlam, hphi, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h3095, h4559, hc01, hc12, hlam, hphi, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h4553, hlam, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [hlam, p4622_0]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h3095, h3633, h4559, hc01, hc12, hlam, hphi, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h3095, h3927, h4559, hc01, hc12, hlam, hphi, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h3633, h4559, h4562, hc01, hc12, hlam, hphi, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h4554, hlam, p4622_0]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h4556, hlam, p4622_0]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [hlam, p4622_0]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h3633, h3927, h4559, h4562, hc01, hc12, hlam, hphi, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4622_1, u5elo0]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h4555, hlam, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h4557, hlam, p4622_0]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [h4558, hlam, p4622_1]
                            · have p4622_0 := h4622c.1
                              have p4622_1 := h4622c.2.1
                              have p4622_2 := h4622c.2.2.1
                              have p4622_3 := h4622c.2.2.2
                              linarith only [hlam, p4622_0]
                      · linarith only [h3927, h4557, h4564, h4565, hc34, hlam, hphi, ht45, u5elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4649 | h4649
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4650 | h4650
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4651 | h4651
                          · rcases h0bigk with h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [hlam, p4652_0]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h0, hlam, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h3095, hlam, p4652_0]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h3633, hlam, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h3927, hlam, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [hlam, p4652_0]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h0, h3095, hc01, hc12, hlam, hphi, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h0, h3633, hc01, hc12, hlam, hphi, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h0, h3927, hc01, hc12, hlam, hphi, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h3095, h4559, hc01, hc12, hlam, hphi, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h4553, hlam, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [hlam, p4652_0]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h3095, h4554, h4559, h4564, h4649, h4651, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h3095, h3927, h4559, hc01, hc12, hlam, hphi, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h3633, h4559, h4562, hc01, hc12, hlam, hphi, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h4554, hlam, p4652_0]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h4556, hlam, p4652_0]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [hlam, p4652_0]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h3633, h3927, h4559, h4562, hc01, hc12, hlam, hphi, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4652_1, u5elo0]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h4555, hlam, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h4557, hlam, p4652_0]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [h4558, hlam, p4652_1]
                            · have p4652_0 := h4652c.1
                              have p4652_1 := h4652c.2.1
                              have p4652_2 := h4652c.2.2.1
                              have p4652_3 := h4652c.2.2.2
                              linarith only [hlam, p4652_0]
                          · linarith only [h4564, h4649, h4651, hc35, hlam, hphi, u5elo4]
                        · linarith only [h3927, h4558, h4564, h4649, h4650, hc35, hlam, hphi, u5elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4680 | h4680
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4681 | h4681
                          · rcases h0bigk with h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c | h4682c
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [hlam, p4682_0]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h0, hlam, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h3095, hlam, p4682_0]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h3633, hlam, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h3927, hlam, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [hlam, p4682_0]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h0, h4556, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h0, h3633, hc01, hc12, hlam, hphi, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h0, h4557, h4649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h3095, h4559, hc01, hc12, hlam, hphi, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h4553, hlam, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [hlam, p4682_0]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h3095, h4554, h4559, h4680, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h3095, h4557, h4559, h4649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h3633, h4559, h4562, hc01, hc12, hlam, hphi, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h4554, hlam, p4682_0]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h4556, hlam, p4682_0]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [hlam, p4682_0]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h3633, h4557, h4559, h4562, h4649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4682_1, u5elo0]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h4555, hlam, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h4557, hlam, p4682_0]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [h4558, hlam, p4682_1]
                            · have p4682_0 := h4682c.1
                              have p4682_1 := h4682c.2.1
                              have p4682_2 := h4682c.2.2.1
                              have p4682_3 := h4682c.2.2.2
                              linarith only [hlam, p4682_0]
                          · linarith only [h4564, h4681, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4709 | h4709
                          · rcases h0bigk with h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c | h4710c
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
                              linarith only [h3095, hlam, p4710_0]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h3633, hlam, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h3927, hlam, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [hlam, p4710_0]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h0, h4556, h4564, h4680, h4709, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h0, h3633, hc01, hc12, hlam, hphi, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h0, h3927, hc01, hc12, hlam, hphi, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h3095, hc01, hc13, hlam, hphi, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h4553, hlam, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [hlam, p4710_0]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h0, h3633, h4553, hc01, hc12, hlam, hphi, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h0, h3927, h4553, hc01, hc12, hlam, hphi, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h3633, h4562, hc01, hc13, hlam, hphi, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h4554, hlam, p4710_0]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h4556, hlam, p4710_0]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [hlam, p4710_0]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h0, h4553, h4556, h4557, h4564, h4680, h4709, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4710_1, u5elo0]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h4555, hlam, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h4557, hlam, p4710_0]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [h4558, hlam, p4710_1]
                            · have p4710_0 := h4710c.1
                              have p4710_1 := h4710c.2.1
                              have p4710_2 := h4710c.2.2.1
                              have p4710_3 := h4710c.2.2.2
                              linarith only [hlam, p4710_0]
                          · linarith only [h4564, h4709, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h3633, h3927, h4558, h4563, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                · linarith only [h3095, h4556, h4562, hlam]
              · linarith only [h0, h4561, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h4554, h4560, hlam]
          · linarith only [h0, h4553, h4559, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4742 | h4742
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4743 | h4743
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4744 | h4744
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4745 | h4745
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4746 | h4746
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4747 | h4747
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4748 | h4748
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4749 | h4749
                        · linarith only [h4554, h4558, h4749, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4751 | h4751
                          · linarith only [h3633, h4553, h4558, h4747, h4751, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · rcases h0bigk with h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c | h4753c
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [hlam, p4753_0]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h0, hlam, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h3095, hlam, p4753_0]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h3633, hlam, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h3927, hlam, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [hlam, p4753_0]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h0, h3095, hc01, hc12, hlam, hphi, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h0, h3633, hc01, hc12, hlam, hphi, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h0, h3927, hc01, hc12, hlam, hphi, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h3095, hc01, hc13, hlam, hphi, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h4553, hlam, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [hlam, p4753_0]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h0, h3633, h4553, hc01, hc12, hlam, hphi, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h0, h3927, h4553, hc01, hc12, hlam, hphi, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h4558, h4746, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4753_1, u5elo1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h4554, hlam, p4753_0]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h4556, hlam, p4753_0]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [hlam, p4753_0]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h4558, hlam, p4753_0]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4753_1, u5elo0]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h4555, hlam, p4753_1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h4557, hlam, p4753_0]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [h4558, h4746, hc04, hlam, hphi, ht45, p4753_1, u5elo1]
                            · have p4753_0 := h4753c.1
                              have p4753_1 := h4753c.2.1
                              have p4753_2 := h4753c.2.2.1
                              have p4753_3 := h4753c.2.2.2
                              linarith only [hlam, p4753_0]
                      · linarith only [h4557, h4558, h4746, h4747, h4748, hc34, hlam, hphi, ht45, u5elo1]
                    · linarith only [h4556, h4558, h4746, h4747, hc23, hlam, hphi, ht34, ht45, u5elo1]
                  · linarith only [h3633, h4746, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h4556, h4558, h4745, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h4744, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h4554, h4743, hlam]
          · linarith only [h0, h4553, h4742, hlam]
      · linarith only [h4556, h4557, hc34, hlam, hphi, ht45, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4787 | h4787
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4788 | h4788
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4789 | h4789
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4790 | h4790
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4791 | h4791
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4792 | h4792
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4793 | h4793
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4794 | h4794
                    · linarith only [h0, h3095, h4553, h4556, h4794, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4796 | h4796
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4797 | h4797
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4798 | h4798
                          · rcases h0bigk with h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c | h4799c
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [hlam, p4799_0]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h0, hlam, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h3095, hlam, p4799_0]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h3633, hlam, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h3927, hlam, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [hlam, p4799_0]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h0, h4553, h4796, h4798, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h0, h4553, h4556, h4796, h4798, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h0, h3927, hc01, hc12, hlam, hphi, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h4556, h4792, hc01, hc13, hlam, hphi, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h4553, hlam, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [hlam, p4799_0]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h4556, hlam, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h3927, h4556, h4792, hc01, hc13, hlam, hphi, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h3633, hc01, hc14, hlam, hphi, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h4554, hlam, p4799_0]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h4556, h4792, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [hlam, p4799_0]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h3927, h4556, h4792, hc01, hc13, hlam, hphi, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4799_1, u5elo0]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h4555, hlam, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h4787, hlam, p4799_0]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [h4788, hlam, p4799_1]
                            · have p4799_0 := h4799c.1
                              have p4799_1 := h4799c.2.1
                              have p4799_2 := h4799c.2.2.1
                              have p4799_3 := h4799c.2.2.2
                              linarith only [hlam, p4799_0]
                          · linarith only [h4556, h4798, hc03, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h4788, h4794, h4796, h4797, hc35, hlam, hphi, u5elo0]
                      · linarith only [h4556, h4787, h4789, h4792, h4796, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h3633, h4556, h4787, h4788, h4789, h4792, h4793, hc01, hc12, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4829 | h4829
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4830 | h4830
                    · linarith only [h3095, h4792, h4830, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4832 | h4832
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4833 | h4833
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4834 | h4834
                          · rcases h0bigk with h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c | h4835c
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [hlam, p4835_0]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h0, hlam, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h3095, hlam, p4835_0]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h3633, hlam, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h3927, hlam, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [hlam, p4835_0]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h0, h4553, h4832, h4834, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h0, h3633, hc01, hc12, hlam, hphi, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h0, h3927, hc01, hc12, hlam, hphi, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h3095, hc01, hc13, hlam, hphi, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h4553, hlam, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [hlam, p4835_0]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h4556, hlam, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h3095, h3927, h4792, hc01, hc34, hlam, hphi, ht12, ht23, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h3633, hc01, hc14, hlam, hphi, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h4554, hlam, p4835_0]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h4556, hc03, hc34, hlam, hphi, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [hlam, p4835_0]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h3927, h4556, hc01, hc34, hlam, hphi, ht12, ht23, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4835_1, u5elo0]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h4555, hlam, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h4787, hlam, p4835_0]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [h4788, hlam, p4835_1]
                            · have p4835_0 := h4835c.1
                              have p4835_1 := h4835c.2.1
                              have p4835_2 := h4835c.2.2.1
                              have p4835_3 := h4835c.2.2.2
                              linarith only [hlam, p4835_0]
                          · linarith only [h4792, h4834, hc13, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h3927, h4788, h4830, h4832, h4833, hc35, hlam, hphi, u5elo1]
                      · linarith only [h4556, h4787, h4832, hc23, hc34, hlam, hphi]
                  · linarith only [h3633, h3927, h4788, h4829, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
              · linarith only [h0, h4555, h4791, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
            · linarith only [h0, h4554, h4790, hlam]
          · linarith only [h0, h4553, h4789, hlam]
        · linarith only [h4556, h4787, h4788, hc35, hlam, hphi, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4869 | h4869
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4870 | h4870
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4871 | h4871
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4872 | h4872
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4873 | h4873
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4874 | h4874
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4875 | h4875
                    · linarith only [h0, h3095, h4553, h4556, h4875, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4877 | h4877
                      · linarith only [h4553, h4787, h4877, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4879 | h4879
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4880 | h4880
                          · rcases h0bigk with h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [hlam, p4881_0]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h0, hlam, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h3095, hlam, p4881_0]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h3633, hlam, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h3927, hlam, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [hlam, p4881_0]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h0, h3095, hc01, hc12, hlam, hphi, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h0, h4554, h4879, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h0, h3095, h4787, hc01, hc12, hlam, hphi, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h4787, h4873, h4880, hc01, hc13, hlam, hphi, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h4553, hlam, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [hlam, p4881_0]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h4556, hlam, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h4787, hlam, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h3633, hc01, hc14, hlam, hphi, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h4554, hlam, p4881_0]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h4556, h4873, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [hlam, p4881_0]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h4556, h4873, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4881_1, u5elo0]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h4555, hlam, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h3095, h3927, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4881_1, u5elo1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [h4869, hlam, p4881_1]
                            · have p4881_0 := h4881c.1
                              have p4881_1 := h4881c.2.1
                              have p4881_2 := h4881c.2.2.1
                              have p4881_3 := h4881c.2.2.2
                              linarith only [hlam, p4881_0]
                          · linarith only [h0, h3633, h4554, h4556, h4879, h4880, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4908 | h4908
                          · rcases h0bigk with h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c | h4909c
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [hlam, p4909_0]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h0, hlam, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h3095, hlam, p4909_0]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h3633, hlam, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h3927, hlam, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [hlam, p4909_0]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h0, h3095, hc01, hc12, hlam, hphi, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h0, h4869, h4875, h4879, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h0, h3927, hc01, hc12, hlam, hphi, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h3095, hc01, hc13, hlam, hphi, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h4553, hlam, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [hlam, p4909_0]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h4556, hlam, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h4787, hlam, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h4556, hc01, hc34, hlam, hphi, ht12, ht23, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h4554, hlam, p4909_0]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h4556, hc03, hc34, hlam, hphi, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [hlam, p4909_0]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h3095, h4556, h4787, hc01, hc34, hlam, hphi, ht12, ht23, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4909_1, u5elo0]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h4555, hlam, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h3095, h3927, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4909_1, u5elo1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [h4869, hlam, p4909_1]
                            · have p4909_0 := h4909c.1
                              have p4909_1 := h4909c.2.1
                              have p4909_2 := h4909c.2.2.1
                              have p4909_3 := h4909c.2.2.2
                              linarith only [hlam, p4909_0]
                          · linarith only [h4556, h4869, h4908, hlam]
                  · linarith only [h3633, h4556, h4869, h4870, h4873, h4874, hc01, hc12, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4937 | h4937
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4938 | h4938
                    · linarith only [h3095, h4873, h4938, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4940 | h4940
                      · linarith only [h4553, h4787, h4940, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4942 | h4942
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4943 | h4943
                          · rcases h0bigk with h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [hlam, p4944_0]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h0, hlam, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h3095, hlam, p4944_0]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h3633, hlam, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h3927, hlam, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [hlam, p4944_0]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h0, h3095, hc01, hc12, hlam, hphi, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h0, h3633, hc01, hc12, hlam, hphi, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h0, h3927, hc01, hc12, hlam, hphi, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h3095, hc01, hc13, hlam, hphi, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h4553, hlam, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [hlam, p4944_0]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h4556, hlam, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h4787, hlam, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h3633, h4873, hc01, hc34, hlam, hphi, ht12, ht23, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h4554, hlam, p4944_0]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h3633, h4873, hc03, hc34, hlam, hphi, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [hlam, p4944_0]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h3095, h3633, h4787, h4873, hc01, hc34, hlam, hphi, ht12, ht23, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4944_1, u5elo0]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h4555, hlam, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h3095, h3927, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4944_1, u5elo1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [h4869, hlam, p4944_1]
                            · have p4944_0 := h4944c.1
                              have p4944_1 := h4944c.2.1
                              have p4944_2 := h4944c.2.2.1
                              have p4944_3 := h4944c.2.2.2
                              linarith only [hlam, p4944_0]
                          · linarith only [h4873, h4943, hc13, hlam, hphi, ht34, ht45, u5elo4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4971 | h4971
                          · rcases h0bigk with h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c | h4972c
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [hlam, p4972_0]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h0, hlam, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h3095, hlam, p4972_0]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h3633, hlam, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h3927, hlam, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [hlam, p4972_0]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h0, h3095, hc01, hc12, hlam, hphi, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h0, h4869, h4938, h4942, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h0, h3927, hc01, hc12, hlam, hphi, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h3095, hc01, hc13, hlam, hphi, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h4553, hlam, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [hlam, p4972_0]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h4556, hlam, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h4787, hlam, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h3633, hc01, hc14, hlam, hphi, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h4554, hlam, p4972_0]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h4556, hc03, hc34, hlam, hphi, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [hlam, p4972_0]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h3095, h4556, h4787, hc01, hc34, hlam, hphi, ht12, ht23, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4972_1, u5elo0]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h4555, hlam, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h3095, h3927, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4972_1, u5elo1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [h4869, hlam, p4972_1]
                            · have p4972_0 := h4972c.1
                              have p4972_1 := h4972c.2.1
                              have p4972_2 := h4972c.2.2.1
                              have p4972_3 := h4972c.2.2.2
                              linarith only [hlam, p4972_0]
                          · linarith only [h4873, h4971, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h3633, h4937, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h4872, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h4554, h4871, hlam]
          · linarith only [h0, h4553, h4870, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5003 | h5003
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5004 | h5004
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5005 | h5005
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5006 | h5006
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5007 | h5007
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5008 | h5008
                    · linarith only [h4553, h4556, h5008, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5010 | h5010
                      · linarith only [h3927, h4553, h4556, h4787, h4869, h5007, h5010, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5012 | h5012
                        · linarith only [h4554, h4869, h5012, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5014 | h5014
                          · linarith only [h3095, h4556, h4869, h5003, h5006, h5014, hc01, hc12, hlam, hphi]
                          · linarith only [h3095, h4556, h5007, h5014, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h3633, h5007, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5018 | h5018
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5019 | h5019
                    · linarith only [h4553, h4787, h5019, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5021 | h5021
                      · linarith only [h4553, h4556, h4869, h5018, h5021, hc35, hlam, hphi, u5elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5023 | h5023
                        · linarith only [h4554, h4869, h5023, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5025 | h5025
                          · rcases h0bigk with h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [hlam, p5026_0]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h0, hlam, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h3095, hlam, p5026_0]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h3633, hlam, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h3927, hlam, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [hlam, p5026_0]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h0, h3095, hc01, hc12, hlam, hphi, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h0, h3633, hc01, hc12, hlam, hphi, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h0, h3633, h4869, hc01, hc12, hlam, hphi, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h3095, hc01, hc13, hlam, hphi, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h4553, hlam, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [hlam, p5026_0]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h4556, hlam, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h4787, hlam, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h4869, h5018, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5026_1, u5elo1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h4554, hlam, p5026_0]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h4869, h5018, hc03, hlam, hphi, ht34, ht45, p5026_1, u5elo1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [hlam, p5026_0]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h4869, hlam, p5026_0]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5026_1, u5elo0]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h4555, hlam, p5026_1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h3095, h3927, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5026_1, u5elo1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [h4869, h5018, hc04, hlam, hphi, ht45, p5026_1, u5elo1]
                            · have p5026_0 := h5026c.1
                              have p5026_1 := h5026c.2.1
                              have p5026_2 := h5026c.2.2.1
                              have p5026_3 := h5026c.2.2.2
                              linarith only [hlam, p5026_0]
                          · linarith only [h5006, h5018, h5025, hlam]
                  · linarith only [h3633, h5018, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h3927, h4555, h5005, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
            · linarith only [h0, h4554, h5004, hlam]
          · linarith only [h0, h4553, h5003, hlam]
  · linarith only [h4553, h4555, hc23, hlam, hphi, ht34, ht45, u5elo2]

end R2N4
