import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_63S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3012000 in
set_option maxHeartbeats 3012000 in
theorem r1l7_11_25_L_0_M_LI_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h480 | h480
  · rcases m.htr 1 2 5 (by decide) (by decide) with h481 | h481
    · rcases m.htr 1 3 5 (by decide) (by decide) with h482 | h482
      · rcases m.htr 1 4 5 (by decide) (by decide) with h483 | h483
        · linarith only [h1, h3, h483, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h485 | h485
          · rcases m.htr 2 3 5 (by decide) (by decide) with h486 | h486
            · rcases m.htr 2 4 5 (by decide) (by decide) with h487 | h487
              · linarith only [h1, h3, h480, h487, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h489 | h489
                · linarith only [h1, h3, h480, h485, h489, hlam]
                · rcases h5bigk with h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hlam, p491_0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hc15, hlam, hphi, p491_1, u5elo0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h3, h485, h487, hc34, hlam, hphi, ht45, p491_1, u5elo4]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h3, hc35, hlam, hphi, p491_1, u5elo4]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h3, hlam, p491_0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h2, hlam, p491_0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hlam, p491_0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h485, h487, hc34, hlam, hphi, ht45, p491_1, u5elo1]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h0, h481, hc35, hlam, hphi, ht01, ht0b, ht5b, p491_1, u1elo0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h483, hlam, p491_0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hc05, hlam, hphi, p491_1, u5elo2]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h481, hlam, p491_1]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hlam, p491_0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h0, h481, h489, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p491_1, u1elo0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h487, hlam, p491_0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hc05, hlam, hphi, p491_1, u5elo3]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h482, hlam, p491_1]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h486, hlam, p491_0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hlam, p491_0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [h489, hlam, p491_0]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hc05, hlam, hphi, p491_1, u5elo4]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hc15, hlam, hphi, p491_1, u5elo4]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hc25, hlam, hphi, p491_1, u5elo4]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hc35, hlam, hphi, p491_1, u5elo4]
                  · have p491_0 := h491c.1
                    have p491_1 := h491c.2.1
                    have p491_2 := h491c.2.2.1
                    have p491_3 := h491c.2.2.2
                    linarith only [hlam, p491_0]
            · linarith only [h2, h482, h485, h486, hc34, hlam, hphi, ht45, u5elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h518 | h518
            · linarith only [h1, h3, h480, h485, h518, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h520 | h520
              · linarith only [h1, h3, h480, h520, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h522 | h522
                · linarith only [h2, h3, h482, h522, hlam]
                · linarith only [h485, h522, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h525 | h525
        · linarith only [h1, h3, h525, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h527 | h527
          · rcases m.htr 2 3 5 (by decide) (by decide) with h528 | h528
            · linarith only [h0, h481, h482, h528, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h527, h528, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h531 | h531
            · linarith only [h0, h480, h527, h531, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h533 | h533
              · linarith only [h1, h3, h480, h533, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h535 | h535
                · rcases h5bigk with h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [hlam, p536_0]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h525, hc14, hlam, hphi, ht45, p536_1, u5elo0]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h3, h527, h533, h535, hc23, hc34, hlam, hphi, p536_1]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h3, h535, hlam, p536_1]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h3, hlam, p536_0]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h2, hlam, p536_0]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [hlam, p536_0]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h527, h533, hc23, hlam, hphi, ht34, ht45, p536_1, u5elo1]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h482, hlam, p536_0]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h525, hlam, p536_0]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h0, h481, hc05, hlam, hphi, ht01, ht0b, ht5b, p536_1, u1elo0]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h481, hlam, p536_1]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [hlam, p536_0]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h531, hlam, p536_1]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h533, hlam, p536_0]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [hc05, hlam, hphi, p536_1, u5elo3]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h481, h527, h533, hc23, hlam, hphi, ht34, ht45, p536_1, u5elo3]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h527, h533, hc23, hlam, hphi, ht34, ht45, p536_1, u5elo3]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [hlam, p536_0]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h1, h3, h480, h527, hc23, hlam, hphi, ht34, ht45, p536_1, u5elo3]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h1, h3, h480, h527, hc23, hlam, hphi, ht34, ht45, p536_1, u5elo4]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h481, h527, h533, hc23, hlam, hphi, ht34, ht45, p536_1, u5elo4]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h527, h533, hc23, hlam, hphi, ht34, ht45, p536_1, u5elo4]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [h535, hlam, p536_1]
                  · have p536_0 := h536c.1
                    have p536_1 := h536c.2.1
                    have p536_2 := h536c.2.2.1
                    have p536_3 := h536c.2.2.2
                    linarith only [hlam, p536_0]
                · linarith only [h527, h535, hc23, hlam, hphi, ht34, ht45, u5elo4]
    · linarith only [h480, h481, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h564 | h564
    · linarith only [h1, h3, h480, h564, hc25, hlam, hphi, u5elo4]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h566 | h566
      · rcases m.htr 1 4 5 (by decide) (by decide) with h567 | h567
        · linarith only [h1, h3, h567, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h569 | h569
          · rcases m.htr 2 3 5 (by decide) (by decide) with h570 | h570
            · rcases m.htr 2 4 5 (by decide) (by decide) with h571 | h571
              · rcases m.htr 3 4 5 (by decide) (by decide) with h572 | h572
                · linarith only [h1, h3, h480, h569, h572, hc12, hc23, hlam, hphi]
                · rcases h5bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hc15, hlam, hphi, p574_1, u5elo0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h3, h571, hlam, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h3, h571, h572, hc34, hlam, hphi, ht45, p574_1, u5elo2]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h3, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h2, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h564, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h572, hc34, hlam, hphi, ht45, p574_1, u5elo1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h567, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hc05, hlam, hphi, p574_1, u5elo2]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hc15, hlam, hphi, p574_1, u5elo2]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h572, hc34, hlam, hphi, ht45, p574_1, u5elo2]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h1, h3, h480, hc12, hlam, hphi, ht23, ht34, ht45, p574_1, u5elo2]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h1, h3, h480, hc12, hlam, hphi, ht23, ht34, ht45, p574_1, u5elo3]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h566, hlam, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h570, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h572, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h1, h3, h480, h571, hc12, hc24, hlam, hphi, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h480, h567, hc12, hlam, hphi, ht23, ht34, ht45, p574_1, u5elo4]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h571, hlam, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h571, hc35, hlam, hphi, p574_1, u5elo2]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hlam, p574_0]
              · linarith only [h480, h571, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h2, h566, h569, h570, hc34, hlam, hphi, ht45, u5elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h602 | h602
            · rcases m.htr 2 4 5 (by decide) (by decide) with h603 | h603
              · rcases m.htr 3 4 5 (by decide) (by decide) with h604 | h604
                · linarith only [h1, h3, h480, h569, h602, h604, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h569, h602, h603, h604, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h480, h603, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h564, h566, h602, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h609 | h609
        · linarith only [h1, h3, h609, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h611 | h611
          · rcases m.htr 2 3 5 (by decide) (by decide) with h612 | h612
            · rcases m.htr 2 4 5 (by decide) (by decide) with h613 | h613
              · rcases m.htr 3 4 5 (by decide) (by decide) with h614 | h614
                · linarith only [h1, h3, h480, h611, h614, hc12, hc23, hlam, hphi]
                · rcases h5bigk with h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hc15, hlam, hphi, p616_1, u5elo0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h3, h613, hlam, p616_1]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h3, h566, h613, hc13, hlam, hphi, ht34, ht45, p616_1, u5elo2]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h3, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h2, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h564, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h566, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h609, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hc05, hlam, hphi, p616_1, u5elo2]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h480, h609, hc12, hlam, hphi, ht23, ht34, ht45, p616_1, u5elo2]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h566, hc13, hlam, hphi, ht34, ht45, p616_1, u5elo2]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h614, hc34, hlam, hphi, ht45, p616_1, u5elo2]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h2, h480, h609, hc12, hlam, hphi, ht23, ht34, ht45, p616_1, u5elo3]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h480, h609, hc12, hlam, hphi, ht23, ht34, ht45, p616_1, u5elo3]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h612, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h614, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h2, h480, h609, h613, hc12, hc24, hlam, hphi, p616_1]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h480, h609, hc12, hlam, hphi, ht23, ht34, ht45, p616_1, u5elo4]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h613, hlam, p616_1]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h613, hc35, hlam, hphi, p616_1, u5elo2]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hlam, p616_0]
              · linarith only [h480, h613, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h611, h612, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h644 | h644
            · linarith only [h566, h611, h644, hc13, hc34, hlam, hphi]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h646 | h646
              · rcases m.htr 3 4 5 (by decide) (by decide) with h647 | h647
                · rcases h5bigk with h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [hlam, p648_0]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h480, h609, hc12, hlam, hphi, ht23, ht34, ht45, p648_1, u5elo0]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h3, h646, hlam, p648_1]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h3, h644, h646, hlam, p648_1]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h3, hlam, p648_0]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h2, hlam, p648_0]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [hlam, p648_0]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h564, hlam, p648_0]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h566, hlam, p648_0]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h609, hlam, p648_0]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [hc05, hlam, hphi, p648_1, u5elo2]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h480, h609, h644, hc12, hlam, hphi, ht23, ht34, ht45, p648_1, u5elo3]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [hlam, p648_0]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h644, hlam, p648_1]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h1, h3, h480, h644, hc12, hlam, hphi, ht23, ht34, ht45, p648_1, u5elo3]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h2, h480, h609, hc12, hlam, hphi, ht23, ht34, ht45, p648_1, u5elo3]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h480, h609, hc12, hlam, hphi, ht23, ht34, ht45, p648_1, u5elo3]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [hc25, hlam, hphi, p648_1, u5elo3]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [hlam, p648_0]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h1, h3, h480, hc12, hlam, hphi, ht23, ht34, ht45, p648_1, u5elo3]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h2, h480, h609, h646, hc12, hc24, hlam, hphi, p648_1]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h480, h609, h646, hc12, hlam, hphi, ht23, ht34, ht45, p648_1, u5elo2]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h646, hlam, p648_1]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [h647, hlam, p648_1]
                  · have p648_0 := h648c.1
                    have p648_1 := h648c.2.1
                    have p648_2 := h648c.2.2.1
                    have p648_3 := h648c.2.2.2
                    linarith only [hlam, p648_0]
                · linarith only [h480, h611, h644, h646, h647, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h480, h646, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]

set_option maxHeartbeats 3012000 in
set_option maxHeartbeats 3012000 in
theorem r1l7_11_25_L_0_M_LI_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_25_L_0_M_LI_x0_x0_x0_x0 m hb1 hb5 h0 h1 h2 h3
  · exact r1l7_11_25_L_0_M_LI_x0_x0_x0_x1 m hb1 hb5 h0 h1 h2 h3

set_option maxHeartbeats 3012000 in
set_option maxHeartbeats 3012000 in
theorem r1l7_11_25_L_0_M_LI_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 3012000 in
set_option maxHeartbeats 3012000 in
theorem r1l7_11_25_L_0_M_LI_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_25_L_0_M_LI_x0_x0_x0 m hb1 hb5 h0 h1 h2
  · exact r1l7_11_25_L_0_M_LI_x0_x0_x1 m hb1 hb5 h0 h1 h2

set_option maxHeartbeats 3012000 in
set_option maxHeartbeats 3012000 in
theorem r1l7_11_25_L_0_M_LI_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h677 | h677
  · rcases m.htr 0 4 5 (by decide) (by decide) with h678 | h678
    · rcases m.htr 1 2 4 (by decide) (by decide) with h679 | h679
      · linarith only [h0, h1, h679, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h681 | h681
        · linarith only [h0, h1, h681, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h683 | h683
          · rcases m.htr 1 4 5 (by decide) (by decide) with h684 | h684
            · rcases m.htr 2 3 4 (by decide) (by decide) with h685 | h685
              · rcases m.htr 2 3 5 (by decide) (by decide) with h686 | h686
                · rcases m.htr 2 4 5 (by decide) (by decide) with h687 | h687
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h688 | h688
                    · rcases h5bigk with h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h681, hc12, hlam, hphi, ht23, ht34, ht45, p689_1, u5elo0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h1, h677, h681, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p689_1, u1elo3]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h1, h677, hc35, hlam, hphi, ht01, ht0b, ht5b, p689_1, u1elo3]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h1, h677, hc45, hlam, hphi, ht01, ht0b, ht5b, p689_1, u1elo3]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h677, hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h681, hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h688, hc45, hlam, hphi, p689_1, u5elo1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h1, h677, hc45, hlam, hphi, ht01, ht0b, ht5b, p689_1, u1elo3]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hc05, hlam, hphi, p689_1, u5elo2]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hc15, hlam, hphi, p689_1, u5elo2]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h688, hc45, hlam, hphi, p689_1, u5elo2]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hc45, hlam, hphi, p689_1, u5elo2]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h677, h681, hc12, hlam, hphi, ht23, ht34, ht45, p689_1, u5elo3]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h683, hlam, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h686, hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h677, h683, hc45, hlam, hphi, p689_1, u5elo0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h678, hlam, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h684, hlam, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h687, hlam, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h688, hlam, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hlam, p689_0]
                    · linarith only [h1, h677, h684, h688, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                  · linarith only [h1, h677, h679, h684, h687, hlam]
                · linarith only [h1, h677, h683, h686, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h718 | h718
                · rcases m.htr 2 4 5 (by decide) (by decide) with h719 | h719
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h720 | h720
                    · rcases h5bigk with h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [hlam, p721_0]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h1, h677, hc15, hlam, hphi, ht01, ht0b, ht5b, p721_1, u1elo3]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h1, h677, hc25, hlam, hphi, ht01, ht0b, ht5b, p721_1, u1elo3]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h1, h677, h720, hc45, hlam, hphi, ht01, ht0b, ht5b, p721_1, u1elo3]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h1, h677, hc45, hlam, hphi, ht01, ht0b, ht5b, p721_1, u1elo3]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h677, hlam, p721_0]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [hlam, p721_0]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h681, hlam, p721_0]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h720, hc45, hlam, hphi, p721_1, u5elo1]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h1, h677, hc45, hlam, hphi, ht01, ht0b, ht5b, p721_1, u1elo3]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [hc05, hlam, hphi, p721_1, u5elo2]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [hc15, hlam, hphi, p721_1, u5elo2]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [hlam, p721_0]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h720, hc45, hlam, hphi, p721_1, u5elo2]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [hc45, hlam, hphi, p721_1, u5elo2]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h677, h681, hc12, hlam, hphi, ht23, ht34, ht45, p721_1, u5elo3]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h683, hlam, p721_1]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h718, hlam, p721_0]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [hlam, p721_0]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h677, h683, hc45, hlam, hphi, p721_1, u5elo0]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h678, hlam, p721_1]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h684, hlam, p721_1]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h719, hlam, p721_1]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [h720, hlam, p721_1]
                      · have p721_0 := h721c.1
                        have p721_1 := h721c.2.1
                        have p721_2 := h721c.2.2.1
                        have p721_3 := h721c.2.2.2
                        linarith only [hlam, p721_0]
                    · linarith only [h685, h720, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h1, h677, h679, h684, h719, hlam]
                · linarith only [h1, h677, h683, h718, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
            · linarith only [h1, h677, h681, h684, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h751 | h751
            · rcases m.htr 2 3 4 (by decide) (by decide) with h752 | h752
              · rcases m.htr 2 3 5 (by decide) (by decide) with h753 | h753
                · rcases m.htr 2 4 5 (by decide) (by decide) with h754 | h754
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h755 | h755
                    · rcases h5bigk with h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [hlam, p756_0]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h1, h677, h681, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p756_1, u1elo3]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h1, h677, h681, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p756_1, u1elo3]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h1, h677, h683, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p756_1, u1elo3]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h1, h677, hc45, hlam, hphi, ht01, ht0b, ht5b, p756_1, u1elo3]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h677, hlam, p756_0]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [hlam, p756_0]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h681, hlam, p756_0]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h683, hlam, p756_0]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [hc45, hlam, hphi, p756_1, u5elo1]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [hc05, hlam, hphi, p756_1, u5elo2]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [hc15, hlam, hphi, p756_1, u5elo2]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [hlam, p756_0]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h683, hc13, hlam, hphi, ht34, ht45, p756_1, u5elo2]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [hc45, hlam, hphi, p756_1, u5elo2]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h677, h681, hc12, hlam, hphi, ht23, ht34, ht45, p756_1, u5elo3]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h681, hc12, hlam, hphi, ht23, ht34, ht45, p756_1, u5elo3]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h753, hlam, p756_0]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [hlam, p756_0]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h753, hc45, hlam, hphi, p756_1, u5elo2]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h678, hlam, p756_1]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h751, hlam, p756_1]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h754, hlam, p756_1]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [h755, hlam, p756_1]
                      · have p756_0 := h756c.1
                        have p756_1 := h756c.2.1
                        have p756_2 := h756c.2.2.1
                        have p756_3 := h756c.2.2.2
                        linarith only [hlam, p756_0]
                    · linarith only [h1, h677, h751, h755, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                  · linarith only [h1, h677, h679, h751, h754, hlam]
                · linarith only [h1, h679, h752, h753, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h785 | h785
                · linarith only [h683, h752, h785, hc13, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h787 | h787
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h788 | h788
                    · rcases h5bigk with h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [hlam, p789_0]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h681, hc12, hlam, hphi, ht23, ht34, ht45, p789_1, u5elo0]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h1, h677, h681, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p789_1, u1elo3]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h1, h677, h681, h785, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p789_1, u1elo3]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h1, h677, hc45, hlam, hphi, ht01, ht0b, ht5b, p789_1, u1elo3]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h677, hlam, p789_0]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [hlam, p789_0]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h681, hlam, p789_0]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h683, hlam, p789_0]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [hc45, hlam, hphi, p789_1, u5elo1]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [hc05, hlam, hphi, p789_1, u5elo2]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h785, hc15, hlam, hphi, p789_1, u5elo3]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [hlam, p789_0]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h785, hlam, p789_1]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h785, hc45, hlam, hphi, p789_1, u5elo3]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h677, h681, hc12, hlam, hphi, ht23, ht34, ht45, p789_1, u5elo3]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h681, hc12, hlam, hphi, ht23, ht34, ht45, p789_1, u5elo3]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [hc25, hlam, hphi, p789_1, u5elo3]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [hlam, p789_0]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [hc45, hlam, hphi, p789_1, u5elo3]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h678, hlam, p789_1]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h751, hlam, p789_1]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h787, hlam, p789_1]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [h788, hlam, p789_1]
                      · have p789_0 := h789c.1
                        have p789_1 := h789c.2.1
                        have p789_2 := h789c.2.2.1
                        have p789_3 := h789c.2.2.2
                        linarith only [hlam, p789_0]
                    · linarith only [h1, h677, h751, h788, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                  · linarith only [h1, h677, h679, h751, h787, hlam]
            · linarith only [h1, h751, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
    · linarith only [h0, h1, h678, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
  · linarith only [h0, h677, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 3012000 in
set_option maxHeartbeats 3012000 in
theorem r1l7_11_25_L_0_M_LI_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_25_L_0_M_LI_x0_x0 m hb1 hb5 h0 h1
  · exact r1l7_11_25_L_0_M_LI_x0_x1 m hb1 hb5 h0 h1

set_option maxHeartbeats 3012000 in
set_option maxHeartbeats 3012000 in
theorem r1l7_11_25_L_0_M_LI_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h820 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h821 | h821
  · rcases m.htr 0 4 5 (by decide) (by decide) with h822 | h822
    · rcases m.htr 1 2 4 (by decide) (by decide) with h823 | h823
      · rcases m.htr 1 2 5 (by decide) (by decide) with h824 | h824
        · rcases m.htr 1 3 5 (by decide) (by decide) with h825 | h825
          · rcases m.htr 1 4 5 (by decide) (by decide) with h826 | h826
            · linarith only [h0, h820, h826, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
            · linarith only [h0, h820, h822, h826, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h829 | h829
            · linarith only [h0, h820, h829, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
            · linarith only [h0, h820, h822, h829, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
        · linarith only [h0, h824, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h820, h823, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h834 | h834
      · rcases m.htr 1 2 5 (by decide) (by decide) with h835 | h835
        · rcases m.htr 1 3 5 (by decide) (by decide) with h836 | h836
          · rcases m.htr 1 4 5 (by decide) (by decide) with h837 | h837
            · linarith only [h0, h820, h837, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h839 | h839
              · rcases m.htr 2 3 5 (by decide) (by decide) with h840 | h840
                · rcases m.htr 2 4 5 (by decide) (by decide) with h841 | h841
                  · linarith only [h820, h822, h834, h841, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h843 | h843
                    · linarith only [h820, h822, h834, h839, h843, hlam]
                    · rcases h5bigk with h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h835, h840, hc35, hlam, hphi, p845_1, u5elo0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h839, h841, hc34, hlam, hphi, ht45, p845_1, u5elo0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h0, h821, h843, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p845_1, u1elo1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h822, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h821, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h839, h841, hc34, hlam, hphi, ht45, p845_1, u5elo1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h0, h821, h843, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p845_1, u1elo1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h837, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hc05, hlam, hphi, p845_1, u5elo2]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h835, hlam, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h843, hc34, hlam, hphi, ht45, p845_1, u5elo2]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h841, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h836, hc05, hlam, hphi, ht01, ht0b, ht5b, p845_1, u1elo2]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h836, hlam, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h840, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h843, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h821, h835, hc25, hlam, hphi, p845_1, u5elo4]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h835, hc25, hlam, hphi, p845_1, u5elo4]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h840, hc35, hlam, hphi, p845_1, u5elo4]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hc35, hlam, hphi, p845_1, u5elo4]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hlam, p845_0]
                · linarith only [h0, h821, h836, h840, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h872 | h872
                · linarith only [h0, h820, h834, h839, h872, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · linarith only [h0, h821, h836, h872, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h875 | h875
            · linarith only [h0, h820, h875, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h877 | h877
              · rcases m.htr 2 3 5 (by decide) (by decide) with h878 | h878
                · linarith only [h0, h821, h835, h836, h878, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h877, h878, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h881 | h881
                · linarith only [h836, h877, h881, hc13, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h883 | h883
                  · linarith only [h820, h822, h834, h883, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h885 | h885
                    · rcases h5bigk with h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [hlam, p886_0]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h875, hc14, hlam, hphi, ht45, p886_1, u5elo0]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h0, h821, hc25, hlam, hphi, ht01, ht0b, ht5b, p886_1, u1elo1]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h0, h820, h821, h822, h834, h877, h885, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p886_1, u1elo1]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h822, hlam, p886_0]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h821, hlam, p886_0]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [hlam, p886_0]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h0, h821, h877, h883, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p886_1, u1elo1]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h836, hlam, p886_0]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h875, hlam, p886_0]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [hc05, hlam, hphi, p886_1, u5elo2]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h835, hlam, p886_1]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [hlam, p886_0]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h881, hlam, p886_1]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h883, hlam, p886_0]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [hc05, hlam, hphi, p886_1, u5elo3]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h835, hc25, hlam, hphi, p886_1, u5elo3]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [hc25, hlam, hphi, p886_1, u5elo3]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [hlam, p886_0]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h820, h822, h834, h877, hc23, hlam, hphi, ht34, ht45, p886_1, u5elo3]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h820, h822, h834, h877, hc23, hlam, hphi, ht34, ht45, p886_1, u5elo4]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h834, h875, h877, hc23, hlam, hphi, ht34, ht45, p886_1, u5elo4]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h877, h883, hc23, hlam, hphi, ht34, ht45, p886_1, u5elo4]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [h885, hlam, p886_1]
                      · have p886_0 := h886c.1
                        have p886_1 := h886c.2.1
                        have p886_2 := h886c.2.2.1
                        have p886_3 := h886c.2.2.2
                        linarith only [hlam, p886_0]
                    · linarith only [h877, h885, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h0, h835, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h820, h834, hlam]
  · linarith only [h820, h821, hc14, hlam, hphi, ht45, u5elo1]

end R2N4
