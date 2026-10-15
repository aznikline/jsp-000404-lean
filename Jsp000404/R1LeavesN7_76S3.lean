import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_76S2

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_0_L_0_L_0_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h412 | h412
  · rcases m.htr 0 4 5 (by decide) (by decide) with h413 | h413
    · rcases m.htr 1 2 4 (by decide) (by decide) with h414 | h414
      · rcases m.htr 1 2 5 (by decide) (by decide) with h415 | h415
        · rcases m.htr 1 3 5 (by decide) (by decide) with h416 | h416
          · rcases m.htr 1 4 5 (by decide) (by decide) with h417 | h417
            · rcases m.htr 2 3 5 (by decide) (by decide) with h418 | h418
              · rcases m.htr 2 4 5 (by decide) (by decide) with h419 | h419
                · rcases m.htr 3 4 5 (by decide) (by decide) with h420 | h420
                  · rcases h5bigk with h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [hlam, p421_0]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h0, h412, h415, h418, h420, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p421_1, u4elo1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h0, h412, h418, h420, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p421_1, u4elo1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h0, h412, h420, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p421_1, u4elo1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h0, h412, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p421_1, u4elo1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h412, hlam, p421_0]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [hlam, p421_0]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h418, h420, hc45, hlam, hphi, ht01, ht0b, ht5b, p421_1, u1elo4]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h0, h412, h420, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p421_1, u4elo1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h0, h412, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p421_1, u4elo1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p421_1, u2elo4]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h415, hlam, p421_1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [hlam, p421_0]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h420, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p421_1, u2elo4]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h0, h412, h415, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p421_1, u4elo1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h418, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p421_1, u2elo2]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h416, hlam, p421_1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h418, hlam, p421_0]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [hlam, p421_0]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h415, h418, hc45, hlam, hphi, ht01, ht0b, ht5b, p421_1, u1elo4]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h413, hlam, p421_1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h417, hlam, p421_1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h419, hlam, p421_1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [h420, hlam, p421_1]
                    · have p421_0 := h421c.1
                      have p421_1 := h421c.2.1
                      have p421_2 := h421c.2.2.1
                      have p421_3 := h421c.2.2.2
                      linarith only [hlam, p421_0]
                  · linarith only [h413, h420, hc34, hlam, hphi, u4elo0]
                · linarith only [h0, h412, h417, h419, hc24, hlam, hphi, u4elo1]
              · linarith only [h0, h412, h416, h418, hc23, hlam, hphi, ht34, u4elo1]
            · linarith only [h0, h417, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
          · linarith only [h0, h412, h416, hc13, hlam, hphi, ht34, u4elo1]
        · linarith only [h0, h414, h415, hc01, hlam, hphi, ht12, u2elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
        · rcases m.htr 1 3 5 (by decide) (by decide) with h454 | h454
          · rcases m.htr 1 4 5 (by decide) (by decide) with h455 | h455
            · rcases m.htr 2 3 5 (by decide) (by decide) with h456 | h456
              · rcases m.htr 2 4 5 (by decide) (by decide) with h457 | h457
                · rcases m.htr 3 4 5 (by decide) (by decide) with h458 | h458
                  · rcases h5bigk with h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h0, h412, h453, h456, h458, hc45, hlam, hphi, ht01, ht0b, ht5b, p459_1, u1elo3]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h0, h412, h414, h456, h458, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p459_1, u4elo2]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h0, h412, h414, h458, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p459_1, u4elo2]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h0, h412, h414, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p459_1, u4elo2]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h412, hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h456, h458, hc45, hlam, hphi, ht01, ht0b, ht5b, p459_1, u1elo4]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h0, h412, h414, h458, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p459_1, u4elo2]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h0, h412, h414, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p459_1, u4elo2]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p459_1, u2elo4]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h453, hlam, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h0, h412, h414, h453, h458, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p459_1, u4elo2]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h0, h412, h414, h453, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p459_1, u4elo2]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h454, hc05, hlam, hphi, ht01, ht0b, ht5b, p459_1, u1elo2]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h454, hlam, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h456, hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h453, h456, hc45, hlam, hphi, ht01, ht0b, ht5b, p459_1, u1elo4]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h413, hlam, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h455, hlam, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h457, hlam, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h458, hlam, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hlam, p459_0]
                  · linarith only [h413, h458, hc34, hlam, hphi, u4elo0]
                · linarith only [h0, h412, h414, h455, h457, hlam]
              · linarith only [h0, h412, h414, h454, h456, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h0, h455, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
          · linarith only [h0, h412, h414, h454, hc13, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h412, h414, h453, hc12, hlam, hphi, ht23, ht34, u4elo2]
    · linarith only [h0, h412, h413, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h492 | h492
    · rcases m.htr 1 2 4 (by decide) (by decide) with h493 | h493
      · rcases m.htr 1 2 5 (by decide) (by decide) with h494 | h494
        · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
          · rcases m.htr 1 4 5 (by decide) (by decide) with h496 | h496
            · rcases m.htr 2 3 5 (by decide) (by decide) with h497 | h497
              · rcases m.htr 2 4 5 (by decide) (by decide) with h498 | h498
                · rcases m.htr 3 4 5 (by decide) (by decide) with h499 | h499
                  · rcases h5bigk with h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h412, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h492, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h0, h492, hc35, hlam, hphi, ht01, ht0b, ht5b, p500_1, u1elo3]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h0, h492, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h496, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h496, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h496, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h496, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h412, hc01, hlam, hphi, ht12, p500_1, u2elo4]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h494, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h494, h499, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p500_1, u2elo1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h493, h498, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p500_1, u2elo1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h412, hc01, hc35, hlam, hphi, ht12, ht23, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h495, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h497, hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h493, h497, h498, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p500_1, u2elo1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h492, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h496, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h498, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h499, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, p500_0]
                  · linarith only [h0, h492, h499, hc34, hlam, hphi, u4elo1]
                · linarith only [h0, h492, h498, hc24, hlam, hphi, u4elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h528 | h528
                · rcases m.htr 3 4 5 (by decide) (by decide) with h529 | h529
                  · rcases h5bigk with h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [hlam, p530_0]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h412, hlam, p530_1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h412, h496, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p530_1, u4elo1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h412, h496, h497, hc23, hlam, hphi, ht34, p530_1, u4elo1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h412, h496, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p530_1, u4elo1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h496, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p530_1, u4elo1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [hlam, p530_0]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h496, h497, hc23, hlam, hphi, ht34, p530_1, u4elo1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h496, h497, hc23, hlam, hphi, ht34, p530_1, u4elo1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h496, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p530_1, u4elo1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h412, hc01, hlam, hphi, ht12, p530_1, u2elo4]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h494, hlam, p530_1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [hlam, p530_0]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h497, hlam, p530_1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p530_1, u2elo4]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h412, h495, hc01, hlam, hphi, p530_1, u1elo2]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h495, hlam, p530_1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h495, hc25, hlam, hphi, ht01, ht0b, ht5b, p530_1, u1elo2]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [hlam, p530_0]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h495, hc45, hlam, hphi, ht01, ht0b, ht5b, p530_1, u1elo2]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h492, hlam, p530_1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h496, hlam, p530_1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h528, hlam, p530_1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [h529, hlam, p530_1]
                    · have p530_0 := h530c.1
                      have p530_1 := h530c.2.1
                      have p530_2 := h530c.2.2.1
                      have p530_3 := h530c.2.2.2
                      linarith only [hlam, p530_0]
                  · linarith only [h0, h492, h529, hc34, hlam, hphi, u4elo1]
                · linarith only [h0, h492, h528, hc24, hlam, hphi, u4elo1]
            · linarith only [h0, h492, h496, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h559 | h559
            · rcases m.htr 2 3 5 (by decide) (by decide) with h560 | h560
              · linarith only [h412, h495, h560, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h562 | h562
                · rcases m.htr 3 4 5 (by decide) (by decide) with h563 | h563
                  · rcases h5bigk with h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [hlam, p564_0]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h412, hlam, p564_1]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h412, h560, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p564_1, u1elo4]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h412, h495, hlam, p564_1]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h412, h495, h563, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p564_1, u4elo3]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h495, h563, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p564_1, u4elo3]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [hlam, p564_0]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h495, h563, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p564_1, u4elo3]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h495, hlam, p564_0]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h495, h563, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p564_1, u4elo3]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h412, hc01, hlam, hphi, ht12, p564_1, u2elo4]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h494, hlam, p564_1]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [hlam, p564_0]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h560, hlam, p564_1]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h493, h562, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p564_1, u2elo1]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h412, h563, hc01, hlam, hphi, ht12, ht23, ht34, p564_1, u4elo3]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h563, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p564_1, u4elo3]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h563, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p564_1, u4elo3]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [hlam, p564_0]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h563, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p564_1, u4elo3]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h492, hlam, p564_1]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h559, hlam, p564_1]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h562, hlam, p564_1]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [h563, hlam, p564_1]
                    · have p564_0 := h564c.1
                      have p564_1 := h564c.2.1
                      have p564_2 := h564c.2.2.1
                      have p564_3 := h564c.2.2.2
                      linarith only [hlam, p564_0]
                  · linarith only [h0, h492, h563, hc34, hlam, hphi, u4elo1]
                · linarith only [h0, h492, h562, hc24, hlam, hphi, u4elo1]
            · linarith only [h0, h492, h559, hlam]
        · linarith only [h0, h493, h494, hc01, hlam, hphi, ht12, u2elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h594 | h594
        · linarith only [h412, h493, h594, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h596 | h596
          · rcases m.htr 1 4 5 (by decide) (by decide) with h597 | h597
            · rcases m.htr 2 3 5 (by decide) (by decide) with h598 | h598
              · rcases m.htr 2 4 5 (by decide) (by decide) with h599 | h599
                · rcases m.htr 3 4 5 (by decide) (by decide) with h600 | h600
                  · rcases h5bigk with h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [hlam, p601_0]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h412, hlam, p601_1]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h594, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p601_1]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h412, h596, hc35, hlam, hphi, ht01, ht0b, ht5b, p601_1, u1elo2]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h412, h597, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p601_1, u4elo1]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h597, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p601_1, u4elo1]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [hlam, p601_0]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h594, hlam, p601_0]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h493, h597, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p601_1, u4elo2]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h493, h597, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p601_1, u4elo2]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h412, h599, hc01, hlam, hphi, ht12, ht23, ht34, p601_1, u4elo2]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h599, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p601_1, u4elo2]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [hlam, p601_0]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h599, h600, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p601_1, u4elo2]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h599, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p601_1, u4elo2]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h412, hc01, hc35, hlam, hphi, ht12, ht23, p601_1]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h596, hlam, p601_1]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h598, hlam, p601_0]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [hlam, p601_0]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h598, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p601_1, u2elo2]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h492, hlam, p601_1]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h597, hlam, p601_1]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h599, hlam, p601_1]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [h600, hlam, p601_1]
                    · have p601_0 := h601c.1
                      have p601_1 := h601c.2.1
                      have p601_2 := h601c.2.2.1
                      have p601_3 := h601c.2.2.2
                      linarith only [hlam, p601_0]
                  · linarith only [h0, h492, h493, h600, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h492, h493, h599, hlam]
              · linarith only [h412, h594, h596, h598, hc01, hlam, hphi, u1elo2]
            · linarith only [h0, h492, h597, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h631 | h631
            · rcases m.htr 2 3 5 (by decide) (by decide) with h632 | h632
              · linarith only [h412, h596, h632, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h634 | h634
                · rcases m.htr 3 4 5 (by decide) (by decide) with h635 | h635
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
                      linarith only [h412, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h412, h594, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h412, h594, h632, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h412, hc45, hlam, hphi, ht01, ht0b, ht5b, p636_1, u1elo4]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p636_1, u1elo4]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h594, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h596, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h493, h631, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p636_1, u4elo2]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h412, h632, h635, hc01, hlam, hphi, ht12, ht23, ht34, p636_1, u4elo3]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h632, h635, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p636_1, u4elo3]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h632, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h632, h635, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p636_1, u4elo3]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h412, h635, hc01, hlam, hphi, ht12, ht23, ht34, p636_1, u4elo3]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h412, h635, hc01, hlam, hphi, ht12, ht23, ht34, p636_1, u4elo3]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h635, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p636_1, u4elo3]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h635, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p636_1, u4elo3]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h492, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h631, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h634, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h635, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                  · linarith only [h0, h492, h493, h635, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h492, h493, h634, hlam]
            · linarith only [h0, h492, h631, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h665 | h665
      · rcases m.htr 1 2 5 (by decide) (by decide) with h666 | h666
        · rcases m.htr 1 3 5 (by decide) (by decide) with h667 | h667
          · rcases m.htr 1 4 5 (by decide) (by decide) with h668 | h668
            · linarith only [h492, h668, hc04, hlam, hphi, u4elo1]
            · linarith only [h0, h668, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h671 | h671
            · linarith only [h0, h492, h671, hc01, hlam, hphi, u1elo3]
            · linarith only [h0, h671, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
        · linarith only [h0, h665, h666, hc01, hlam, hphi, ht12, u2elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h675 | h675
        · linarith only [h412, h665, h675, hc01, hlam, hphi, ht12, u2elo3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h677 | h677
          · rcases m.htr 1 4 5 (by decide) (by decide) with h678 | h678
            · linarith only [h0, h492, h678, hc01, hlam, hphi, u1elo3]
            · linarith only [h0, h678, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h681 | h681
            · linarith only [h0, h492, h681, hc01, hlam, hphi, u1elo3]
            · linarith only [h0, h681, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]

theorem r1l7_11_12_14_25_L_0_L_0_L_0_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_0_L_0_L_0_H_I_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_0_L_0_L_0_H_I_x1 m hb1 hb2 hb4 hb5 h0

theorem r1l7_11_13_25_L_R_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h10, h16, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h0, h10, h13, h16, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                                  · linarith only [h0, h10, h19, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h0, h10, h13, h19, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                              · linarith only [h0, h13, h14, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                              · linarith only [h13, h23, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                                  · linarith only [h13, h26, hc23, hlam, hphi, ht12, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                                    · linarith only [h10, h23, h28, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                                      · linarith only [h0, h11, h30, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                      · linarith only [h2, h25, h26, h30, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                                  · linarith only [h0, h10, h33, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                                    · linarith only [h0, h10, h35, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                                      · linarith only [h11, h25, h37, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                                        · linarith only [h13, h25, h39, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                        · linarith only [h0, h13, h39, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                          · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h10, h11, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                          · linarith only [h0, h10, h4, h45, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h48 | h48
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                                · linarith only [h0, h10, h4, h44, h49, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                                  · linarith only [h0, h10, h4, h44, h51, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h10, h44, h47, h51, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h4, h47, h48, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h10, h44, h47, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                          · linarith only [h0, h44, h5, h56, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                                        · linarith only [h1, h58, h64, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                        · linarith only [h1, h58, h60, h64, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                      · linarith only [h44, h60, h63, hlam]
                                    · linarith only [h10, h59, h62, hlam]
                                  · linarith only [h10, h59, h61, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                                      · linarith only [h44, h60, h70, h72, hc23, hlam, hphi, ht12, u1ehi1]
                                      · linarith only [h0, h4, h44, h7, h72, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                    · linarith only [h1, h59, h71, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                  · linarith only [h10, h59, h70, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h58, h59, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                              · linarith only [h0, h4, h58, h7, h78, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                                  · linarith only [h0, h10, h4, h58, h81, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                  · linarith only [h10, h81, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                                  · linarith only [h0, h10, h4, h58, h84, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                  · linarith only [h10, h84, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h87 | h87
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h91 | h91
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                                · linarith only [h2, h9, h92, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                                  · linarith only [h0, h87, h94, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h1, h90, h94, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                              · linarith only [h90, h91, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h7, h9, h90, hc45, hlam, hphi, ht34, u3ehi1]
                          · linarith only [h0, h6, h87, h89, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h5, h87, h88, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
                          · linarith only [h0, h102, h4, h87, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                                · linarith only [h106, h2, h9, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                                  · linarith only [h0, h101, h108, h4, h87, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h101, h104, h108, h87, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h104, h105, h4, h8, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h101, h104, h7, h87, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
                        · linarith only [h101, h5, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h115 | h115
                  · linarith only [h115, h7, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h121 | h121
                            · linarith only [h1, h115, h121, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h123 | h123
                              · linarith only [h1, h115, h123, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h125 | h125
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                                  · linarith only [h1, h118, h126, h7, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h128 | h128
                                    · linarith only [h1, h115, h118, h128, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h130 | h130
                                      · linarith only [h0, h119, h130, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                      · linarith only [h125, h126, h130, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · linarith only [h117, h125, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h0, h118, h120, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h118, h119, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h118, h4, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h139 | h139
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
                            · linarith only [h1, h117, h140, h7, hc45, hlam, hphi, ht34, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h142 | h142
                              · linarith only [h1, h115, h142, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h144 | h144
                                · linarith only [h117, h144, h2, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                                  · linarith only [h1, h137, h146, h7, hc12, hlam, hphi, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
                                    · linarith only [h1, h115, h137, h148, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                                      · linarith only [h0, h117, h138, h150, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h152 | h152
                                        · linarith only [h1, h117, h152, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                        · linarith only [h1, h152, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                          · linarith only [h0, h137, h139, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h137, h138, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h137, h4, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h158 | h158
                · rcases m.htr 0 3 5 (by decide) (by decide) with h159 | h159
                  · linarith only [h159, h4, h6, hlam]
                  · linarith only [h158, h159, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h162 | h162
                  · linarith only [h158, h162, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
                    · linarith only [h164, h5, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
                          · linarith only [h0, h168, h6, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                            · linarith only [h1, h158, h170, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
                              · linarith only [h1, h162, h172, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h174 | h174
                                · linarith only [h1, h158, h164, h174, hc14, hlam, hphi, u1ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h176 | h176
                                  · linarith only [h0, h1, h158, h166, h176, h6, hc25, hlam, hphi, ht12, u1ehi2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                                    · linarith only [h0, h1, h162, h167, h176, h178, h6, hc25, hlam, hphi, ht12, u1ehi2]
                                    · linarith only [h0, h167, h176, h178, h6, hc35, hlam, hphi, u3ehi2]
                        · linarith only [h167, h5, h6, hc12, hc25, hlam, hphi]
                      · linarith only [h166, h4, h6, hc25, hlam, hphi, ht12, u1ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h183 | h183
              · rcases m.htr 0 3 4 (by decide) (by decide) with h184 | h184
                · linarith only [h184, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h186 | h186
                  · linarith only [h184, h186, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h188 | h188
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h190 | h190
                        · linarith only [h183, h190, h5, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h192 | h192
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h193 | h193
                            · linarith only [h1, h184, h193, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h195 | h195
                              · linarith only [h1, h186, h195, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h197 | h197
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                                  · linarith only [h0, h184, h189, h198, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                                  · linarith only [h0, h189, h198, h5, hc34, hlam, hphi, u3ehi2]
                                · linarith only [h0, h184, h188, h189, h197, h5, hc24, hc34, hlam, hphi, ht12, u1ehi3, u3ehi2]
                          · linarith only [h183, h189, h192, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h189, h4, h5, hc24, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h188, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h205 | h205
                · linarith only [h205, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h207 | h207
                  · linarith only [h205, h207, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h209 | h209
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
                        · linarith only [h0, h211, h5, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
                          · linarith only [h0, h183, h213, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                            · linarith only [h1, h205, h215, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h217 | h217
                              · linarith only [h1, h207, h217, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h220 | h220
                                  · linarith only [h0, h1, h205, h210, h220, h5, hc24, hlam, hphi, ht12, u1ehi2]
                                  · linarith only [h0, h210, h220, h5, hc34, hlam, hphi, u3ehi2]
                                · linarith only [h209, h219, h5, hc24, hlam, hphi, ht12, u1ehi3]
                      · linarith only [h210, h4, h5, hc24, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h209, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h226 | h226
            · rcases m.htr 0 2 5 (by decide) (by decide) with h227 | h227
              · rcases m.htr 0 3 4 (by decide) (by decide) with h228 | h228
                · rcases m.htr 0 3 5 (by decide) (by decide) with h229 | h229
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h230 | h230
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h231 | h231
                      · linarith only [h226, h230, h231, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h233 | h233
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h234 | h234
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h236 | h236
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h237 | h237
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h238 | h238
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h239 | h239
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h240 | h240
                                      · linarith only [h0, h233, h240, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                      · linarith only [h2, h237, h238, h240, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                    · linarith only [h0, h234, h239, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                  · linarith only [h0, h234, h238, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                · linarith only [h226, h230, h237, h4, hc23, hlam, hphi, ht12, u1ehi3]
                              · linarith only [h229, h231, h234, h236, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                            · linarith only [h228, h231, h234, h235, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · linarith only [h227, h234, h4, hc12, hc23, hlam, hphi]
                        · linarith only [h226, h233, h4, hc23, hlam, hphi, ht12, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h250 | h250
                      · linarith only [h227, h250, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h252 | h252
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h253 | h253
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h254 | h254
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h255 | h255
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h256 | h256
                                · linarith only [h2, h230, h256, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h258 | h258
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h259 | h259
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h260 | h260
                                      · linarith only [h0, h230, h252, h260, h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h262 | h262
                                        · linarith only [h0, h2, h230, h253, h258, h260, h262, h4, hc23, hlam, hphi, ht12, u1ehi3]
                                        · rcases h5bigk with h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c | h264c
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [hlam, p264_0]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h227, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p264_1, u5ehi1]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h227, h258, h260, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p264_1, u3ehi3]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h227, h262, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p264_1, u3ehi3]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h230, hlam, p264_1]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h3, hlam, p264_0]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [hlam, p264_0]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h258, h260, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p264_1, u3ehi3]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h227, h262, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p264_1, u3ehi3]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h256, hlam, p264_1]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h227, hlam, p264_1]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h253, hlam, p264_1]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [hlam, p264_0]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h227, h262, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p264_1, u3ehi3]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h260, hlam, p264_1]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h229, hlam, p264_0]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h255, hlam, p264_0]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h259, hlam, p264_0]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [hlam, p264_0]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h262, hlam, p264_1]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h3, hc45, hlam, hphi, ht12, ht23, ht34, p264_1, u1ehi4]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h0, h252, h258, h4, hc23, hc45, hlam, hphi, ht12, ht34, p264_1, u1ehi4, u3ehi3]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h259, h262, hc45, hlam, hphi, ht34, p264_1, u3ehi3]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [h262, hc45, hlam, hphi, ht34, p264_1, u3ehi3]
                                          · have p264_0 := h264c.1
                                            have p264_1 := h264c.2.1
                                            have p264_2 := h264c.2.2.1
                                            have p264_3 := h264c.2.2.2
                                            linarith only [hlam, p264_0]
                                    · linarith only [h0, h253, h259, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                  · linarith only [h0, h253, h254, h258, h4, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                              · linarith only [h227, h229, h255, h4, hc23, hlam, hphi, ht12, u1ehi2]
                            · linarith only [h228, h250, h253, h254, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · linarith only [h227, h253, h4, hc12, hc23, hlam, hphi]
                        · linarith only [h226, h252, h4, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h228, h229, hc35, hlam, hphi, u3ehi3]
                · linarith only [h226, h228, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h298 | h298
                · rcases m.htr 0 3 5 (by decide) (by decide) with h299 | h299
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h300 | h300
                    · linarith only [h226, h227, h300, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
                      · linarith only [h0, h302, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                          · linarith only [h0, h227, h305, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h308 | h308
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                                · linarith only [h2, h300, h309, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h312 | h312
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h313 | h313
                                      · linarith only [h0, h2, h227, h300, h304, h312, h313, hc23, hlam, hphi, ht12, u1ehi3]
                                      · linarith only [h0, h227, h304, h311, h313, hc45, hlam, hphi, ht34, u3ehi3]
                                    · linarith only [h1, h308, h312, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                  · linarith only [h0, h311, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h307, h308, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h298, h302, h304, h307, h4, hc23, hlam, hphi, ht12, u1ehi3]
                        · linarith only [h226, h227, h304, hc12, hc25, hlam, hphi]
                  · linarith only [h298, h299, hc35, hlam, hphi, u3ehi3]
                · linarith only [h226, h298, h4, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h323 | h323
              · rcases m.htr 0 3 4 (by decide) (by decide) with h324 | h324
                · rcases m.htr 0 3 5 (by decide) (by decide) with h325 | h325
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h326 | h326
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h327 | h327
                      · linarith only [h0, h327, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h329 | h329
                        · linarith only [h0, h226, h329, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h333 | h333
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h334 | h334
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h337 | h337
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h338 | h338
                                        · linarith only [h1, h332, h338, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                        · linarith only [h2, h334, h338, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                      · linarith only [h2, h226, h334, h337, hlam]
                                    · linarith only [h0, h331, h336, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                  · linarith only [h0, h331, h335, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                · linarith only [h326, h329, h331, h334, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                              · linarith only [h332, h333, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h324, h332, h4, hc23, hlam, hphi, ht12, u1ehi2]
                          · linarith only [h323, h331, h4, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h226, h323, h326, hlam]
                  · linarith only [h324, h325, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h350 | h350
                  · linarith only [h324, h350, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h323, h350, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h353 | h353
                · rcases m.htr 0 3 5 (by decide) (by decide) with h354 | h354
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h355 | h355
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h356 | h356
                      · linarith only [h0, h356, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h358 | h358
                        · linarith only [h0, h226, h358, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h360 | h360
                          · linarith only [h0, h323, h360, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h362 | h362
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h363 | h363
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h364 | h364
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h365 | h365
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h366 | h366
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h367 | h367
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h368 | h368
                                        · linarith only [h1, h362, h368, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                        · linarith only [h2, h364, h368, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                      · linarith only [h2, h226, h364, h367, hlam]
                                    · linarith only [h1, h363, h366, h4, hlam]
                                  · linarith only [h1, h363, h365, h4, hc34, hlam, hphi, u3ehi4]
                                · linarith only [h353, h355, h364, h4, hc23, hlam, hphi, ht12, u1ehi3]
                              · linarith only [h362, h363, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h353, h362, h4, hc23, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h377 | h377
                      · linarith only [h0, h377, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h379 | h379
                        · linarith only [h0, h226, h379, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h381 | h381
                          · linarith only [h0, h323, h381, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h383 | h383
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h384 | h384
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h385 | h385
                                · linarith only [h2, h355, h385, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h387 | h387
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h388 | h388
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h389 | h389
                                      · linarith only [h2, h355, h387, h389, hc23, hlam, hphi, ht12, u1ehi3]
                                      · linarith only [h0, h226, h389, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                    · linarith only [h1, h384, h388, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                  · linarith only [h1, h384, h387, h4, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h383, h384, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h353, h383, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h353, h354, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h397 | h397
                  · linarith only [h353, h397, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h399 | h399
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h400 | h400
                      · linarith only [h0, h4, h400, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h402 | h402
                        · linarith only [h0, h226, h402, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h404 | h404
                          · linarith only [h1, h323, h353, h400, h404, hc02, hc34, hlam, hphi, ht23]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                            · linarith only [h1, h353, h406, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h408 | h408
                              · linarith only [h1, h397, h408, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                                  · linarith only [h1, h353, h411, hc23, hlam, hphi, ht12, u1ehi2]
                                  · linarith only [h0, h4, h411, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h226, h399, h410, hc24, hlam, hphi, ht12, u1ehi3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h415 | h415
                      · linarith only [h0, h4, h415, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h417 | h417
                        · linarith only [h0, h226, h417, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h419 | h419
                          · linarith only [h0, h323, h419, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h421 | h421
                            · linarith only [h1, h353, h421, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h423 | h423
                              · linarith only [h1, h353, h399, h423, hc45, hlam, hphi, ht34, u3ehi4]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h425 | h425
                                · linarith only [h1, h353, h399, h425, hc14, hlam, hphi, u1ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h427 | h427
                                  · linarith only [h0, h353, h4, h427, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h0, h4, h427, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h1, h2, hc14, hlam, hphi, u1ehi2]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h433 | h433
    · linarith only [h0, h433, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h435 | h435
      · linarith only [h0, h435, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h437 | h437
        · linarith only [h0, h437, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h439 | h439
          · rcases m.htr 0 2 4 (by decide) (by decide) with h440 | h440
            · rcases m.htr 0 2 5 (by decide) (by decide) with h441 | h441
              · rcases m.htr 0 3 4 (by decide) (by decide) with h442 | h442
                · rcases m.htr 0 3 5 (by decide) (by decide) with h443 | h443
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h444 | h444
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h445 | h445
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h446 | h446
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h448 | h448
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h449 | h449
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h450 | h450
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h451 | h451
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h452 | h452
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h453 | h453
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h454 | h454
                                        · linarith only [h439, h451, h454, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                        · linarith only [h0, h439, h451, h453, h454, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h457 | h457
                                        · linarith only [h0, h439, h451, h453, h457, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                        · rcases h5bigk with h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [hlam, p459_0]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h437, hlam, p459_1]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            rcases p459_3 (m.d 0 5) (by simp) with h462 | h462
                                            · rcases p459_3 (m.d 1 5) (by simp) with h463 | h463
                                              · rcases p459_3 (m.d 2 5) (by simp) with h464 | h464
                                                · linarith only [h441, h464, hlam]
                                                · rcases p459_3 (m.d 3 5) (by simp) with h466 | h466
                                                  · linarith only [h443, h466, hlam]
                                                  · rcases p459_3 (m.d 4 5) (by simp) with h468 | h468
                                                    · linarith only [h444, h468, hlam]
                                                    · linarith only [h453, h468, hlam]
                                              · linarith only [h447, h463, hlam]
                                            · linarith only [h441, h462, hlam]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            rcases p459_3 (m.d 0 5) (by simp) with h473 | h473
                                            · rcases p459_3 (m.d 1 5) (by simp) with h474 | h474
                                              · rcases p459_3 (m.d 2 5) (by simp) with h475 | h475
                                                · linarith only [h441, h475, hlam]
                                                · linarith only [h452, h475, hlam]
                                              · linarith only [h449, h474, hlam]
                                            · linarith only [h443, h473, hlam]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h437, h445, h448, h450, h451, h453, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p459_1, u3ehi3]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h437, h445, h448, h450, hc12, hlam, hphi, p459_1, u1ehi0]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [hlam, p459_0]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            rcases p459_3 (m.d 0 5) (by simp) with h483 | h483
                                            · linarith only [h437, h483, hlam]
                                            · linarith only [h441, h483, hlam]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            rcases p459_3 (m.d 0 5) (by simp) with h486 | h486
                                            · linarith only [h437, h486, hlam]
                                            · linarith only [h443, h486, hlam]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h445, h448, h450, h451, h453, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p459_1, u3ehi3]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h441, hlam, p459_1]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h447, hlam, p459_1]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [hlam, p459_0]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h0, h441, h457, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p459_1, u3ehi3]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h453, hlam, p459_1]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h443, hlam, p459_0]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h449, hlam, p459_0]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h452, hlam, p459_0]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [hlam, p459_0]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h457, hlam, p459_1]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h444, hlam, p459_0]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h450, hlam, p459_0]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h433, h442, h444, h445, hc12, hlam, hphi, ht01, ht0b, ht5b, p459_1, u5ehi2]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [h433, h442, h444, h445, h457, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p459_1, u3ehi3]
                                          · have p459_0 := h459c.1
                                            have p459_1 := h459c.2.1
                                            have p459_2 := h459c.2.2.1
                                            have p459_3 := h459c.2.2.2
                                            linarith only [hlam, p459_0]
                                    · linarith only [h433, h443, h445, h451, h452, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h506 | h506
                                    · linarith only [h451, h506, hc34, hlam, hphi, u3ehi4]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h508 | h508
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h509 | h509
                                        · rcases h5bigk with h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [hlam, p510_0]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h437, hlam, p510_1]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            rcases p510_3 (m.d 0 5) (by simp) with h513 | h513
                                            · rcases p510_3 (m.d 1 5) (by simp) with h514 | h514
                                              · rcases p510_3 (m.d 2 5) (by simp) with h515 | h515
                                                · linarith only [h441, h515, hlam]
                                                · rcases p510_3 (m.d 3 5) (by simp) with h517 | h517
                                                  · linarith only [h443, h517, hlam]
                                                  · linarith only [h506, h517, hlam]
                                              · linarith only [h447, h514, hlam]
                                            · linarith only [h441, h513, hlam]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h437, h445, h448, h450, h506, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p510_1, u3ehi2]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            rcases p510_3 (m.d 0 5) (by simp) with h523 | h523
                                            · rcases p510_3 (m.d 1 5) (by simp) with h524 | h524
                                              · rcases p510_3 (m.d 2 5) (by simp) with h525 | h525
                                                · linarith only [h441, h525, hlam]
                                                · linarith only [h508, h525, hlam]
                                              · linarith only [h450, h524, hlam]
                                            · linarith only [h444, h523, hlam]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h437, h445, h448, h450, hc12, hlam, hphi, p510_1, u1ehi0]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [hlam, p510_0]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            rcases p510_3 (m.d 0 5) (by simp) with h532 | h532
                                            · linarith only [h437, h532, hlam]
                                            · linarith only [h441, h532, hlam]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h445, h448, h450, h506, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p510_1, u3ehi2]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            rcases p510_3 (m.d 0 5) (by simp) with h536 | h536
                                            · linarith only [h437, h536, hlam]
                                            · linarith only [h444, h536, hlam]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h441, hlam, p510_1]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h447, hlam, p510_1]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [hlam, p510_0]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h506, hlam, p510_1]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h0, h441, hc12, hlam, hphi, ht01, ht0b, ht5b, p510_1, u5ehi4]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h443, hlam, p510_0]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h449, hlam, p510_0]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h433, h443, h445, hc12, hlam, hphi, ht01, ht0b, ht5b, p510_1, u5ehi2]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [hlam, p510_0]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h433, h442, h445, h509, hc12, hlam, hphi, ht01, ht0b, ht5b, p510_1, u5ehi4]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h444, hlam, p510_0]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h450, hlam, p510_0]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h508, hlam, p510_0]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [h509, hlam, p510_0]
                                          · have p510_0 := h510c.1
                                            have p510_1 := h510c.2.1
                                            have p510_2 := h510c.2.2.1
                                            have p510_3 := h510c.2.2.2
                                            linarith only [hlam, p510_0]
                                        · linarith only [h0, h440, h508, h509, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h555 | h555
                                        · linarith only [h433, h442, h445, h451, h508, h555, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                        · linarith only [h433, h442, h444, h445, h451, h555, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · linarith only [h433, h442, h444, h445, h450, hc12, hlam, hphi, u1ehi3]
                              · linarith only [h433, h449, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                            · linarith only [h433, h448, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h0, h447, hc25, hlam, hphi, ht12, u1ehi0]
                        · linarith only [h0, h446, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h445, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h564 | h564
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h565 | h565
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h566 | h566
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h567 | h567
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h568 | h568
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h569 | h569
                                · linarith only [h435, h444, h564, h567, h569, hc12, hlam, hphi, u1ehi0]
                                · linarith only [h435, h569, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                              · linarith only [h0, h439, h443, h568, hc12, hlam, hphi, u1ehi2]
                            · linarith only [h433, h443, h567, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h0, h566, hc25, hlam, hphi, ht12, u1ehi0]
                        · linarith only [h0, h440, h565, hlam]
                      · linarith only [h0, h564, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h442, h443, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h578 | h578
                  · linarith only [h442, h578, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h580 | h580
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h581 | h581
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h582 | h582
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h583 | h583
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h584 | h584
                            · linarith only [h433, h442, h581, h584, hc12, hlam, hphi, u1ehi0]
                            · linarith only [h433, h584, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h0, h441, h583, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                        · linarith only [h0, h440, h582, hlam]
                      · linarith only [h0, h581, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h590 | h590
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h591 | h591
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h592 | h592
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h593 | h593
                            · linarith only [h433, h442, h590, h593, hc12, hlam, hphi, u1ehi0]
                            · linarith only [h433, h593, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h0, h441, h592, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                        · linarith only [h0, h440, h441, h580, h591, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · linarith only [h0, h439, h590, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h599 | h599
                · rcases m.htr 0 3 5 (by decide) (by decide) with h600 | h600
                  · linarith only [h439, h441, h600, hlam]
                  · linarith only [h599, h600, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h603 | h603
                  · linarith only [h599, h603, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h605 | h605
                    · linarith only [h440, h441, h605, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h607 | h607
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h608 | h608
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h609 | h609
                          · linarith only [h439, h441, h609, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h0, h609, hc25, hlam, hphi, ht12, u1ehi0]
                        · linarith only [h433, h440, h607, h608, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                      · linarith only [h0, h607, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h614 | h614
              · rcases m.htr 0 3 4 (by decide) (by decide) with h615 | h615
                · linarith only [h439, h440, h615, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h617 | h617
                  · linarith only [h615, h617, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h619 | h619
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h620 | h620
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h621 | h621
                        · linarith only [h439, h440, h621, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h621, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h439, h620, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h439, h440, h619, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h626 | h626
                · linarith only [h439, h440, h626, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h628 | h628
                  · linarith only [h626, h628, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h630 | h630
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h631 | h631
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h632 | h632
                        · linarith only [h0, h440, h632, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h0, h632, hc24, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h439, h631, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h439, h440, h630, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h637 | h637
            · rcases m.htr 0 2 5 (by decide) (by decide) with h638 | h638
              · rcases m.htr 0 3 4 (by decide) (by decide) with h639 | h639
                · rcases m.htr 0 3 5 (by decide) (by decide) with h640 | h640
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h641 | h641
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h642 | h642
                      · linarith only [h439, h637, h641, h642, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · linarith only [h0, h642, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h645 | h645
                      · linarith only [h0, h439, h645, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h645, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h639, h640, hc35, hlam, hphi, u3ehi3]
                · linarith only [h439, h637, h639, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h650 | h650
                · rcases m.htr 0 3 5 (by decide) (by decide) with h651 | h651
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h652 | h652
                    · linarith only [h637, h638, h652, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h654 | h654
                      · linarith only [h0, h439, h654, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h654, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h650, h651, hc35, hlam, hphi, u3ehi3]
                · linarith only [h439, h637, h650, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h659 | h659
              · rcases m.htr 0 3 4 (by decide) (by decide) with h660 | h660
                · rcases m.htr 0 3 5 (by decide) (by decide) with h661 | h661
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h662 | h662
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h663 | h663
                      · linarith only [h439, h659, h663, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h663, hc23, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h637, h659, h662, hlam]
                  · linarith only [h660, h661, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h668 | h668
                  · linarith only [h660, h668, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h439, h659, h668, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h671 | h671
                · rcases m.htr 0 3 5 (by decide) (by decide) with h672 | h672
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h673 | h673
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h674 | h674
                      · linarith only [h0, h439, h674, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h674, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h677 | h677
                      · linarith only [h0, h439, h677, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h677, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h671, h672, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h681 | h681
                  · linarith only [h671, h681, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h683 | h683
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h684 | h684
                      · linarith only [h0, h439, h684, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h684, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h687 | h687
                      · linarith only [h0, h439, h687, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h687, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
