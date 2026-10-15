import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_25_L_0_L_0_H_I_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h688 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h689 | h689
  · rcases m.htr 1 2 5 (by decide) (by decide) with h690 | h690
    · rcases m.htr 1 3 5 (by decide) (by decide) with h691 | h691
      · rcases m.htr 2 3 5 (by decide) (by decide) with h692 | h692
        · rcases m.htr 2 4 5 (by decide) (by decide) with h693 | h693
          · rcases m.htr 3 4 5 (by decide) (by decide) with h694 | h694
            · rcases h5bigk with h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [hlam, p695_0]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h0, hlam, p695_1]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h692, h694, hc45, hlam, hphi, ht0b, ht5b, p695_1, u0elo4]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h0, h690, h694, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p695_1, u2elo1]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h0, h690, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p695_1, u2elo1]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h690, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p695_1, u2elo1]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [hlam, p695_0]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h690, h692, h694, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p695_1, u2elo1]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h690, h694, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p695_1, u2elo1]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h690, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p695_1, u2elo1]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h688, hlam, p695_1]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h690, hlam, p695_1]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [hlam, p695_0]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h688, h694, hc45, hlam, hphi, ht0b, ht5b, p695_1, u0elo1]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h688, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p695_1, u2elo0]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h689, hlam, p695_0]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h691, hlam, p695_0]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h692, hlam, p695_0]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [hlam, p695_0]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h689, hc45, hlam, hphi, ht0b, ht5b, p695_1, u0elo2]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p695_1]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h688, h692, h694, hc15, hlam, hphi, ht0b, ht5b, p695_1, u0elo4]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h693, hlam, p695_0]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [h694, hlam, p695_0]
              · have p695_0 := h695c.1
                have p695_1 := h695c.2.1
                have p695_2 := h695c.2.2.1
                have p695_3 := h695c.2.2.2
                linarith only [hlam, p695_0]
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
                linarith only [h0, hlam, p721_1]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p721_1, u0elo4]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h688, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p721_1, u2elo0]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h0, h690, h694, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p721_1, u2elo1]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h690, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p721_1, u2elo1]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [hlam, p721_0]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h690, h693, h694, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p721_1, u2elo1]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h690, h694, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p721_1, u2elo1]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h690, h694, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p721_1, u2elo1]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h688, hlam, p721_1]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h690, hlam, p721_1]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [hlam, p721_0]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h688, h694, hc34, hlam, hphi, ht0b, ht45, ht5b, p721_1, u0elo4]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h688, h694, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p721_1, u2elo0]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h689, hlam, p721_0]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h691, hlam, p721_0]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h692, hlam, p721_0]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [hlam, p721_0]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h694, hlam, p721_1]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p721_1]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h688, h693, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p721_1, u2elo0]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h693, hlam, p721_0]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [h688, h693, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p721_1, u2elo0]
              · have p721_0 := h721c.1
                have p721_1 := h721c.2.1
                have p721_2 := h721c.2.2.1
                have p721_3 := h721c.2.2.2
                linarith only [hlam, p721_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h747 | h747
            · linarith only [h692, h693, h747, hlam]
            · rcases h5bigk with h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h0, hlam, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p749_1, u0elo4]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p749_1, u0elo4]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h0, h690, h747, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p749_1, u2elo1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h690, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p749_1, u2elo1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h690, h692, h747, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p749_1, u2elo1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h690, h747, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p749_1, u2elo1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h690, h747, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p749_1, u2elo1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h688, hlam, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h690, hlam, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h747, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p749_1, u2elo4]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h693, hlam, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h689, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h691, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h692, hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hlam, p749_0]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h747, hlam, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h692, h747, hc34, hc45, hlam, hphi, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [h747, hc34, hc45, hlam, hphi, p749_1]
              · have p749_0 := h749c.1
                have p749_1 := h749c.2.1
                have p749_2 := h749c.2.2.1
                have p749_3 := h749c.2.2.2
                linarith only [hlam, p749_0]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h775 | h775
          · rcases m.htr 3 4 5 (by decide) (by decide) with h776 | h776
            · rcases h5bigk with h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [hlam, p777_0]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h0, hlam, p777_1]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p777_1, u0elo4]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h688, h692, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p777_1, u2elo0]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h0, h690, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p777_1, u2elo1]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h690, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p777_1, u2elo1]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [hlam, p777_0]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h690, h692, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p777_1, u2elo1]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h690, h692, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p777_1, u2elo1]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h690, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p777_1, u2elo1]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h688, hlam, p777_1]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h690, hlam, p777_1]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [hlam, p777_0]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h692, hlam, p777_1]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p777_1, u2elo4]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h689, hlam, p777_0]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h691, hlam, p777_0]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h689, hc25, hlam, hphi, ht0b, ht5b, p777_1, u0elo2]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [hlam, p777_0]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h689, hc45, hlam, hphi, ht0b, ht5b, p777_1, u0elo2]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p777_1]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h0, h775, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p777_1, u2elo4]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h775, hlam, p777_0]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [h776, hlam, p777_0]
              · have p777_0 := h777c.1
                have p777_1 := h777c.2.1
                have p777_2 := h777c.2.2.1
                have p777_3 := h777c.2.2.2
                linarith only [hlam, p777_0]
            · linarith only [h692, h775, h776, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h804 | h804
            · rcases h5bigk with h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [hlam, p805_0]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h0, hlam, p805_1]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p805_1, u0elo4]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h688, h775, h804, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p805_1, u2elo0]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h0, h690, h775, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p805_1, u2elo1]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h690, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p805_1, u2elo1]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [hlam, p805_0]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h690, h692, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p805_1, u2elo1]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h690, h775, h804, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p805_1, u2elo1]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h690, h775, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p805_1, u2elo1]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h688, hlam, p805_1]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h690, hlam, p805_1]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [hlam, p805_0]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h692, hlam, p805_1]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h775, hlam, p805_1]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h689, hlam, p805_0]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h691, hlam, p805_0]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h689, h692, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p805_1, u0elo4]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [hlam, p805_0]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h689, h775, hc24, hlam, hphi, ht0b, ht45, ht5b, p805_1, u0elo2]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h804, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p805_1]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h689, h804, hc15, hlam, hphi, ht0b, ht5b, p805_1, u0elo2]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h689, h692, h804, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p805_1, u0elo2]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [h804, hlam, p805_0]
              · have p805_0 := h805c.1
                have p805_1 := h805c.2.1
                have p805_2 := h805c.2.2.1
                have p805_3 := h805c.2.2.2
                linarith only [hlam, p805_0]
            · rcases h5bigk with h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [hlam, p831_0]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h0, hlam, p831_1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h692, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p831_1, u0elo4]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h688, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p831_1, u2elo0]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h0, h690, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p831_1, u2elo1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h690, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p831_1, u2elo1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [hlam, p831_0]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h690, h692, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p831_1, u2elo1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h690, h692, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p831_1, u2elo1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h690, h692, h804, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p831_1, u2elo1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h688, hlam, p831_1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h690, hlam, p831_1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [hlam, p831_0]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h692, hlam, p831_1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h775, hlam, p831_1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h689, hlam, p831_0]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h691, hlam, p831_0]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h689, h692, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p831_1, u0elo4]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [hlam, p831_0]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h804, hlam, p831_1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p831_1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p831_1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h692, hc23, hc45, hlam, hphi, ht34, p831_1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [h804, hc34, hc45, hlam, hphi, p831_1]
              · have p831_0 := h831c.1
                have p831_1 := h831c.2.1
                have p831_2 := h831c.2.2.1
                have p831_3 := h831c.2.2.2
                linarith only [hlam, p831_0]
      · linarith only [h0, h689, h691, hlam]
    · linarith only [h688, h690, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h859 | h859
    · rcases m.htr 1 3 5 (by decide) (by decide) with h860 | h860
      · rcases m.htr 2 3 5 (by decide) (by decide) with h861 | h861
        · linarith only [h688, h689, h861, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h863 | h863
          · rcases m.htr 3 4 5 (by decide) (by decide) with h864 | h864
            · rcases h5bigk with h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h0, hlam, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p865_1, u0elo4]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h689, hlam, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h689, h859, h860, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p865_1, u2elo1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h859, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p865_1, u2elo1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h859, h861, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p865_1, u2elo1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h859, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p865_1, u2elo1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h859, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p865_1, u2elo1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h688, hlam, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h859, hlam, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h861, hlam, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p865_1, u2elo4]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h0, h864, hc01, hc34, hlam, hphi, ht12, ht23, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h860, hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h859, h860, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p865_1, u2elo1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h859, h860, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p865_1, u2elo1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h0, h863, hc01, hlam, hphi, ht12, p865_1, u2elo3]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h863, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p865_1, u2elo4]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h863, hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h864, hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hlam, p865_0]
            · linarith only [h688, h689, h863, h864, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h892 | h892
            · rcases h5bigk with h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [hlam, p893_0]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h0, hlam, p893_1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p893_1, u0elo4]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h689, hlam, p893_1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h689, h859, h860, h863, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p893_1, u2elo1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h859, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p893_1, u2elo1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [hlam, p893_0]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h859, h861, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p893_1, u2elo1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h859, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p893_1, u2elo1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h859, h863, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p893_1, u2elo1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h688, hlam, p893_1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h859, hlam, p893_1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [hlam, p893_0]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h861, hlam, p893_1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h863, hlam, p893_1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p893_1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h860, hlam, p893_0]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h859, h860, h861, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p893_1, u2elo1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [hlam, p893_0]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h859, h860, h863, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p893_1, u2elo1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p893_1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h860, h892, hlam, p893_1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h859, h860, h861, h892, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p893_1, u2elo1]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [h892, hlam, p893_0]
              · have p893_0 := h893c.1
                have p893_1 := h893c.2.1
                have p893_2 := h893c.2.2.1
                have p893_3 := h893c.2.2.2
                linarith only [hlam, p893_0]
            · rcases h5bigk with h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [hlam, p919_0]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h0, hlam, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h861, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p919_1, u0elo4]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h689, hlam, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h689, h859, h860, h892, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p919_1, u2elo1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h859, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p919_1, u2elo1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [hlam, p919_0]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h859, h861, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p919_1, u2elo1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h859, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p919_1, u2elo1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h689, h859, h892, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p919_1, u2elo1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h688, hlam, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h859, hlam, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [hlam, p919_0]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h861, hlam, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h863, hlam, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h860, hlam, p919_0]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h859, h860, h861, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p919_1, u2elo1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [hlam, p919_0]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h892, hlam, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h861, hc23, hc45, hlam, hphi, ht34, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [h689, hc03, hc45, hlam, hphi, ht34, p919_1]
              · have p919_0 := h919c.1
                have p919_1 := h919c.2.1
                have p919_2 := h919c.2.2.1
                have p919_3 := h919c.2.2.2
                linarith only [hlam, p919_0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h945 | h945
        · linarith only [h0, h860, h945, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h947 | h947
          · rcases m.htr 3 4 5 (by decide) (by decide) with h948 | h948
            · rcases h5bigk with h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h0, hlam, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h945, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p949_1, u0elo4]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h689, hlam, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p949_1, u0elo4]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h859, h945, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p949_1, u2elo1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h860, hlam, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h859, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p949_1, u2elo1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h688, hlam, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h859, hlam, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h945, hlam, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p949_1, u2elo4]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h0, h948, hc01, hc34, hlam, hphi, ht12, ht23, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h0, h948, hc01, hc34, hlam, hphi, ht12, ht23, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h945, h948, hc23, hc34, hlam, hphi, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                rcases p949_3 (m.d 0 5) (by simp) with h969 | h969
                · linarith only [h689, h969, hlam]
                · linarith only [h688, h947, h969, hlam]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h688, h947, hlam, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h0, h688, h947, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p949_1, u0elo4]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h947, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h948, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hlam, p949_0]
            · linarith only [h688, h689, h947, h948, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h978 | h978
            · rcases h5bigk with h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c | h979c
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [hlam, p979_0]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h0, hlam, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p979_1, u0elo4]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h689, hlam, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h0, h859, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p979_1, u2elo1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h859, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p979_1, u2elo1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [hlam, p979_0]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h859, h945, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p979_1, u2elo1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h860, hlam, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h859, h947, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p979_1, u2elo1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h688, hlam, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h859, hlam, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [hlam, p979_0]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h945, hlam, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h947, hlam, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h945, hc23, hc35, hlam, hphi, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [hlam, p979_0]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h947, h978, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h0, h978, hc01, hc34, hlam, hphi, ht12, ht23, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h945, h978, hc23, hc34, hlam, hphi, p979_1]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [h978, hlam, p979_0]
              · have p979_0 := h979c.1
                have p979_1 := h979c.2.1
                have p979_2 := h979c.2.2.1
                have p979_3 := h979c.2.2.2
                linarith only [hlam, p979_0]
            · rcases h5bigk with h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [hlam, p1005_0]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h0, hlam, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h945, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1005_1, u0elo4]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h689, hlam, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h978, hc34, hlam, hphi, ht0b, ht45, ht5b, p1005_1, u0elo4]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h859, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1005_1, u2elo1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [hlam, p1005_0]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h859, h945, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1005_1, u2elo1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h860, hlam, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h860, h978, hlam, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h688, hlam, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h859, hlam, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [hlam, p1005_0]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h945, hlam, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h947, hlam, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h0, h978, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h945, h978, hc23, hc45, hlam, hphi, ht34, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [hlam, p1005_0]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h978, hlam, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h945, hc23, hc45, hlam, hphi, ht34, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [h689, hc03, hc45, hlam, hphi, ht34, p1005_1]
              · have p1005_0 := h1005c.1
                have p1005_1 := h1005c.2.1
                have p1005_2 := h1005c.2.2.1
                have p1005_3 := h1005c.2.2.2
                linarith only [hlam, p1005_0]
    · linarith only [h688, h859, hc12, hlam, hphi, u2elo0]

end R2N4
