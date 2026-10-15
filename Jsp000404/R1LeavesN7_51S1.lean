import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_51S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5216000 in
theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h3 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
  · rcases m.htr 1 2 5 (by decide) (by decide) with h478 | h478
    · rcases m.htr 1 3 4 (by decide) (by decide) with h479 | h479
      · rcases m.htr 1 3 5 (by decide) (by decide) with h480 | h480
        · rcases m.htr 1 4 5 (by decide) (by decide) with h481 | h481
          · linarith only [h0, h3, h481, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
            · rcases m.htr 2 3 5 (by decide) (by decide) with h484 | h484
              · rcases m.htr 2 4 5 (by decide) (by decide) with h485 | h485
                · linarith only [h477, h479, h481, h483, h485, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h487 | h487
                  · linarith only [h479, h481, h487, hlam]
                  · rcases h5bigk with h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [hlam, p489_0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h1, h478, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p489_1, u2elo0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p489_1, u2elo0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p489_1, u2elo0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h3, hlam, p489_0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h0, hlam, p489_0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [hlam, p489_0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p489_1]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h0, h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p489_1, u2elo0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h481, hlam, p489_0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h1, hlam, p489_1]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h478, hlam, p489_1]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [hlam, p489_0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p489_1, u2elo4]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h485, hlam, p489_0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h2, hlam, p489_1]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h480, hlam, p489_1]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h484, hlam, p489_0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [hlam, p489_0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h487, hlam, p489_0]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h3, hc04, hc45, hlam, hphi, p489_1]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h479, h481, hc34, hc45, hlam, hphi, p489_1]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h485, hc24, hc45, hlam, hphi, p489_1]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [h487, hc34, hc45, hlam, hphi, p489_1]
                    · have p489_0 := h489c.1
                      have p489_1 := h489c.2.1
                      have p489_2 := h489c.2.2.1
                      have p489_3 := h489c.2.2.2
                      linarith only [hlam, p489_0]
              · linarith only [h477, h480, h483, h484, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h516 | h516
              · linarith only [h477, h479, h483, h516, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h518 | h518
                · linarith only [h479, h481, h483, h518, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h520 | h520
                  · linarith only [h479, h481, h520, hlam]
                  · rcases h5bigk with h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c | h522c
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [hlam, p522_0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p522_1, u2elo0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h1, h518, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p522_1, u2elo0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h1, h483, h520, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p522_1, u2elo0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h3, hlam, p522_0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h0, hlam, p522_0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [hlam, p522_0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h0, h518, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p522_1]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h0, h1, h483, h520, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p522_1, u2elo0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h481, hlam, p522_0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h1, hlam, p522_1]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h478, hlam, p522_1]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [hlam, p522_0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h516, hlam, p522_1]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h518, hlam, p522_0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h2, hlam, p522_1]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h480, hlam, p522_1]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h483, h518, hc23, hc35, hlam, hphi, p522_1]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [hlam, p522_0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h520, hlam, p522_0]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h1, h483, h518, hc23, hc45, hlam, hphi, ht34, p522_1]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h478, h483, h518, hc23, hc45, hlam, hphi, ht34, p522_1]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h483, h518, hc23, hc45, hlam, hphi, ht34, p522_1]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [h516, hc23, hc45, hlam, hphi, ht34, p522_1]
                    · have p522_0 := h522c.1
                      have p522_1 := h522c.2.1
                      have p522_2 := h522c.2.2.1
                      have p522_3 := h522c.2.2.2
                      linarith only [hlam, p522_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h548 | h548
          · linarith only [h1, h2, h3, h479, h480, h548, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h550 | h550
            · rcases m.htr 2 3 5 (by decide) (by decide) with h551 | h551
              · linarith only [h477, h480, h551, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h553 | h553
                · linarith only [h2, h3, h477, h480, h550, h553, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h555 | h555
                  · linarith only [h2, h3, h477, h480, h550, h555, hlam]
                  · rcases h5bigk with h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [hlam, p557_0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p557_1, u2elo0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h1, h550, h551, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p557_1, u2elo0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h1, h477, h480, h550, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p557_1, u2elo0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h3, hlam, p557_0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h0, hlam, p557_0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [hlam, p557_0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h550, h551, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p557_1]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h480, hlam, p557_0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h548, hlam, p557_0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h1, hlam, p557_1]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h478, hlam, p557_1]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [hlam, p557_0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h551, hlam, p557_1]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h553, hlam, p557_0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h2, hlam, p557_1]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h2, hc03, hc15, hlam, hphi, ht0b, ht5b, p557_1]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h1, h2, h550, h551, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p557_1, u2elo0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [hlam, p557_0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h555, hlam, p557_0]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h0, h478, h550, h551, hc34, hc45, hlam, hphi, p557_1]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h478, h550, h551, hc34, hc45, hlam, hphi, p557_1]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h550, h551, hc34, hc45, hlam, hphi, p557_1]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [h477, h480, h550, hc34, hc45, hlam, hphi, p557_1]
                    · have p557_0 := h557c.1
                      have p557_1 := h557c.2.1
                      have p557_2 := h557c.2.2.1
                      have p557_3 := h557c.2.2.2
                      linarith only [hlam, p557_0]
            · linarith only [h479, h480, h550, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h584 | h584
        · rcases m.htr 1 4 5 (by decide) (by decide) with h585 | h585
          · linarith only [h0, h3, h585, hlam]
          · linarith only [h479, h584, h585, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h588 | h588
          · linarith only [h0, h3, h588, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h590 | h590
            · linarith only [h477, h479, h590, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h592 | h592
              · linarith only [h477, h584, h592, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h594 | h594
                · linarith only [h1, h3, h594, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h596 | h596
                  · linarith only [h2, h3, h596, hlam]
                  · rcases h5bigk with h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [hlam, p598_0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p598_1, u2elo0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p598_1, u2elo0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h1, h478, h584, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p598_1, u2elo0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h3, hlam, p598_0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h0, hlam, p598_0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [hlam, p598_0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p598_1]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h584, hlam, p598_0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h588, hlam, p598_0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h1, hlam, p598_1]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h478, hlam, p598_1]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [hlam, p598_0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h592, hlam, p598_1]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h594, hlam, p598_0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h2, hlam, p598_1]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h2, hc03, hc15, hlam, hphi, ht0b, ht5b, p598_1]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h1, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p598_1, u2elo0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [hlam, p598_0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h596, hlam, p598_0]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h0, h477, h479, h588, hc23, hc45, hlam, hphi, ht34, p598_1]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h477, h479, h588, hc23, hc45, hlam, hphi, ht34, p598_1]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h592, hc23, hc45, hlam, hphi, ht34, p598_1]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [h477, h584, hc23, hc45, hlam, hphi, ht34, p598_1]
                    · have p598_0 := h598c.1
                      have p598_1 := h598c.2.1
                      have p598_2 := h598c.2.2.1
                      have p598_3 := h598c.2.2.2
                      linarith only [hlam, p598_0]
    · linarith only [h1, h478, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h625 | h625
    · rcases m.htr 1 3 4 (by decide) (by decide) with h626 | h626
      · rcases m.htr 1 3 5 (by decide) (by decide) with h627 | h627
        · rcases m.htr 1 4 5 (by decide) (by decide) with h628 | h628
          · linarith only [h0, h3, h628, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h630 | h630
            · rcases m.htr 2 3 5 (by decide) (by decide) with h631 | h631
              · rcases m.htr 2 4 5 (by decide) (by decide) with h632 | h632
                · linarith only [h477, h625, h626, h628, h632, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h634 | h634
                  · linarith only [h626, h628, h634, hlam]
                  · rcases h5bigk with h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p636_1, u2elo0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h1, h631, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p636_1, u2elo0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p636_1, u2elo0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h3, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h0, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h0, h631, hc01, hc35, hlam, hphi, ht0b, ht5b, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h477, h625, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p636_1, u2elo2]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h628, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h1, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h625, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p636_1, u2elo4]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h632, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h2, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h627, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h631, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h634, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h3, hc04, hc45, hlam, hphi, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h626, h628, hc34, hc45, hlam, hphi, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h632, hc24, hc45, hlam, hphi, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h634, hc34, hc45, hlam, hphi, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
              · linarith only [h1, h2, h477, h631, hc12, hlam, hphi, u2elo0]
            · linarith only [h477, h626, h630, hlam]
        · linarith only [h477, h625, h627, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h665 | h665
        · rcases m.htr 1 4 5 (by decide) (by decide) with h666 | h666
          · linarith only [h0, h3, h666, hlam]
          · linarith only [h477, h625, h626, h666, hlam]
        · linarith only [h477, h625, h665, hlam]
    · linarith only [h1, h625, hc12, hlam, hphi, u2elo0]

set_option maxHeartbeats 5216000 in
theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3
  · exact r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3

set_option maxHeartbeats 5216000 in
theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h671 | h671
  · rcases m.htr 1 2 3 (by decide) (by decide) with h672 | h672
    · rcases m.htr 1 2 5 (by decide) (by decide) with h673 | h673
      · rcases m.htr 1 3 4 (by decide) (by decide) with h674 | h674
        · rcases m.htr 1 3 5 (by decide) (by decide) with h675 | h675
          · linarith only [h0, h2, h675, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h677 | h677
            · linarith only [h674, h675, h677, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h679 | h679
              · rcases m.htr 2 3 5 (by decide) (by decide) with h680 | h680
                · linarith only [h2, h672, h680, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h682 | h682
                  · linarith only [h672, h675, h677, h679, h682, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h684 | h684
                    · linarith only [h672, h675, h677, h679, h684, hlam]
                    · linarith only [h2, h671, h684, hlam]
              · linarith only [h674, h675, h679, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h688 | h688
          · linarith only [h2, h674, h688, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h690 | h690
            · rcases m.htr 2 3 4 (by decide) (by decide) with h691 | h691
              · linarith only [h672, h674, h691, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h693 | h693
                · linarith only [h2, h672, h674, h693, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h695 | h695
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h696 | h696
                    · rcases h5bigk with h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [hlam, p697_0]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h1, h688, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p697_1, u2elo0]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h1, h693, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p697_1, u2elo0]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h2, hlam, p697_0]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p697_1, u2elo0]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h0, hlam, p697_0]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [hlam, p697_0]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h0, h693, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p697_1]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h688, hlam, p697_0]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h0, h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p697_1, u2elo0]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h1, hlam, p697_1]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h673, hlam, p697_1]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [hlam, p697_0]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h693, hlam, p697_1]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p697_1, u2elo4]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h2, h696, hc03, hc34, hlam, hphi, p697_1]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h672, h688, h696, hc23, hc34, hlam, hphi, p697_1]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h693, h696, hc23, hc34, hlam, hphi, p697_1]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [hlam, p697_0]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        rcases p697_3 (m.d 0 5) (by simp) with h717 | h717
                        · linarith only [h2, h717, hlam]
                        · linarith only [h671, h717, hlam]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h671, hlam, p697_1]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h690, hlam, p697_1]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h695, hlam, p697_1]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [h696, hlam, p697_1]
                      · have p697_0 := h697c.1
                        have p697_1 := h697c.2.1
                        have p697_2 := h697c.2.2.1
                        have p697_3 := h697c.2.2.2
                        linarith only [hlam, p697_0]
                    · linarith only [h674, h690, h696, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h726 | h726
                    · rcases h5bigk with h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [hlam, p727_0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h1, h690, h691, h695, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p727_1, u2elo0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h1, h691, h695, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p727_1, u2elo0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h2, hlam, p727_0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h1, h691, h695, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p727_1, u2elo0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h0, hlam, p727_0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [hlam, p727_0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h0, h691, h695, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h688, hlam, p727_0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h0, h1, h691, h695, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p727_1, u2elo0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h1, hlam, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h673, hlam, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [hlam, p727_0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h693, hlam, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h695, hlam, p727_0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h1, h691, h695, h726, hc23, hc34, hlam, hphi, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h673, h691, h695, h726, hc23, hc34, hlam, hphi, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h691, h695, h726, hc23, hc34, hlam, hphi, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [hlam, p727_0]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h691, h695, h726, hc23, hc34, hlam, hphi, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h671, hlam, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h690, hlam, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h690, h691, h695, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [h726, hlam, p727_1]
                      · have p727_0 := h727c.1
                        have p727_1 := h727c.2.1
                        have p727_2 := h727c.2.2.1
                        have p727_3 := h727c.2.2.2
                        linarith only [hlam, p727_0]
                    · linarith only [h674, h690, h726, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h754 | h754
              · linarith only [h672, h674, h754, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h756 | h756
                · linarith only [h2, h672, h674, h756, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h758 | h758
                  · linarith only [h673, h690, h758, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h760 | h760
                    · rcases h5bigk with h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [hlam, p761_0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p761_1, u2elo0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p761_1, u2elo0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h2, hlam, p761_0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h1, h758, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p761_1, u2elo0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h0, hlam, p761_0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [hlam, p761_0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p761_1]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h688, hlam, p761_0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h690, hlam, p761_0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h1, hlam, p761_1]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h673, hlam, p761_1]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [hlam, p761_0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h756, hlam, p761_1]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h758, hlam, p761_0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h2, hc03, hc35, hlam, hphi, p761_1]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h672, h688, hc23, hc35, hlam, hphi, p761_1]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h756, hc23, hc35, hlam, hphi, p761_1]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [hlam, p761_0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h672, h674, h690, h760, hc23, hc34, hlam, hphi, p761_1]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h671, hlam, p761_1]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h672, h674, h690, hc23, hc45, hlam, hphi, ht34, p761_1]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h1, h671, h754, h758, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p761_1, u2elo0]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [h760, hlam, p761_1]
                      · have p761_0 := h761c.1
                        have p761_1 := h761c.2.1
                        have p761_2 := h761c.2.2.1
                        have p761_3 := h761c.2.2.2
                        linarith only [hlam, p761_0]
                    · linarith only [h2, h671, h760, hlam]
      · linarith only [h1, h673, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h789 | h789
      · rcases m.htr 1 3 4 (by decide) (by decide) with h790 | h790
        · rcases m.htr 1 3 5 (by decide) (by decide) with h791 | h791
          · linarith only [h0, h2, h791, hlam]
          · linarith only [h672, h789, h791, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h794 | h794
          · linarith only [h2, h790, h794, hc03, hc34, hlam, hphi]
          · linarith only [h672, h789, h794, hlam]
      · linarith only [h1, h789, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h798 | h798
    · rcases m.htr 1 2 5 (by decide) (by decide) with h799 | h799
      · rcases m.htr 1 3 4 (by decide) (by decide) with h800 | h800
        · rcases m.htr 1 3 5 (by decide) (by decide) with h801 | h801
          · linarith only [h0, h2, h801, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h803 | h803
            · linarith only [h0, h671, h800, h801, h803, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h805 | h805
              · rcases m.htr 2 3 5 (by decide) (by decide) with h806 | h806
                · linarith only [h2, h798, h806, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h808 | h808
                  · linarith only [h0, h671, h798, h801, h805, h808, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h810 | h810
                    · linarith only [h0, h671, h798, h801, h805, h810, hlam]
                    · rcases h5bigk with h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [hlam, p812_0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h798, h801, h805, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p812_1, u2elo0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h2, hlam, p812_0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h671, hlam, p812_0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h0, hlam, p812_0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [hlam, p812_0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h801, hlam, p812_0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h803, hlam, p812_0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h1, hlam, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h799, hlam, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [hlam, p812_0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h806, hlam, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h808, hlam, p812_0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h2, h810, hc03, hc45, hlam, hphi, ht34, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h798, h801, h805, h810, hc34, hc45, hlam, hphi, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h805, h806, h810, hc34, hc45, hlam, hphi, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [hlam, p812_0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h810, hlam, p812_0]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h0, h798, h801, h805, hc34, hc45, hlam, hphi, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h798, h801, h805, hc34, hc45, hlam, hphi, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h805, h806, hc34, hc45, hlam, hphi, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [h2, hc03, hc45, hlam, hphi, ht34, p812_1]
                      · have p812_0 := h812c.1
                        have p812_1 := h812c.2.1
                        have p812_2 := h812c.2.2.1
                        have p812_3 := h812c.2.2.2
                        linarith only [hlam, p812_0]
              · linarith only [h800, h801, h805, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h839 | h839
          · linarith only [h2, h800, h839, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h841 | h841
            · linarith only [h0, h671, h841, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h843 | h843
              · linarith only [h798, h800, h843, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h845 | h845
                · linarith only [h2, h798, h845, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h847 | h847
                  · linarith only [h0, h671, h799, h847, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h849 | h849
                    · rcases h5bigk with h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [hlam, p850_0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p850_1, u2elo0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p850_1, u2elo0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h2, hlam, p850_0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h671, hlam, p850_0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h0, hlam, p850_0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [hlam, p850_0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h839, hlam, p850_0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h841, hlam, p850_0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h1, hlam, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h799, hlam, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [hlam, p850_0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h845, hlam, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h847, hlam, p850_0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h2, hc03, hc35, hlam, hphi, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h798, h839, hc23, hc35, hlam, hphi, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h845, hc23, hc35, hlam, hphi, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [hlam, p850_0]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h671, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h0, h798, h800, h841, hc23, hc45, hlam, hphi, ht34, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h798, h800, h841, hc23, hc45, hlam, hphi, ht34, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h845, hc23, hc45, hlam, hphi, ht34, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [h849, hlam, p850_1]
                      · have p850_0 := h850c.1
                        have p850_1 := h850c.2.1
                        have p850_2 := h850c.2.2.1
                        have p850_3 := h850c.2.2.2
                        linarith only [hlam, p850_0]
                    · rcases h5bigk with h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [hlam, p876_0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h1, h798, h800, h841, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p876_1, u2elo0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h1, h843, h847, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p876_1, u2elo0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h2, hlam, p876_0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h671, hlam, p876_0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h0, hlam, p876_0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [hlam, p876_0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h0, h843, h847, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p876_1]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h839, hlam, p876_0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h841, hlam, p876_0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h1, hlam, p876_1]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h799, hlam, p876_1]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [hlam, p876_0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h845, hlam, p876_1]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h847, hlam, p876_0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h1, h843, h847, h849, hc23, hc45, hlam, hphi, ht34, p876_1]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h799, h843, h847, h849, hc23, hc45, hlam, hphi, ht34, p876_1]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h843, h847, h849, hc23, hc45, hlam, hphi, ht34, p876_1]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [hlam, p876_0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h849, hlam, p876_0]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h0, h799, h843, h847, hc23, hc45, hlam, hphi, ht34, p876_1]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h799, h843, h847, hc23, hc45, hlam, hphi, ht34, p876_1]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h843, h847, hc23, hc45, hlam, hphi, ht34, p876_1]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [h2, hc03, hc45, hlam, hphi, ht34, p876_1]
                      · have p876_0 := h876c.1
                        have p876_1 := h876c.2.1
                        have p876_2 := h876c.2.2.1
                        have p876_3 := h876c.2.2.2
                        linarith only [hlam, p876_0]
      · linarith only [h1, h799, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h903 | h903
      · rcases m.htr 1 3 4 (by decide) (by decide) with h904 | h904
        · rcases m.htr 1 3 5 (by decide) (by decide) with h905 | h905
          · linarith only [h0, h2, h905, hlam]
          · linarith only [h798, h903, h905, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h908 | h908
          · linarith only [h2, h904, h908, hc03, hc34, hlam, hphi]
          · linarith only [h798, h903, h908, hlam]
      · linarith only [h1, h903, hc12, hlam, hphi, u2elo0]

set_option maxHeartbeats 5216000 in
theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2
  · exact r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2

end R2N4
