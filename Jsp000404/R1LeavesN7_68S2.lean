import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_68S1

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_0_M_LI_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h628 | h628
  · rcases m.htr 0 3 5 (by decide) (by decide) with h629 | h629
    · rcases m.htr 0 4 5 (by decide) (by decide) with h630 | h630
      · rcases m.htr 1 2 5 (by decide) (by decide) with h631 | h631
        · rcases m.htr 1 4 5 (by decide) (by decide) with h632 | h632
          · rcases m.htr 2 3 5 (by decide) (by decide) with h633 | h633
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
                    linarith only [h0, hlam, p636_1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h633, h635, hc45, hlam, hphi, p636_1, u5elo0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h635, hc45, hlam, hphi, p636_1, u5elo0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h0, hc45, hlam, hphi, p636_1, u5elo1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [hc05, hlam, hphi, p636_1, u5elo1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h633, h635, hc45, hlam, hphi, p636_1, u5elo1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h635, hc45, hlam, hphi, p636_1, u5elo1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [hc45, hlam, hphi, p636_1, u5elo1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h628, hlam, p636_1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h631, hlam, p636_1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h635, hc45, hlam, hphi, p636_1, u5elo2]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h628, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p636_1, u2elo0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h629, hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [hc15, hlam, hphi, p636_1, u5elo3]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h633, hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h629, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p636_1, u3elo0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h630, hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h632, hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h634, hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h635, hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [hlam, p636_0]
                · rcases h5bigk with h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [hlam, p662_0]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h0, hlam, p662_1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [hc25, hlam, hphi, p662_1, u5elo0]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h0, hc35, hlam, hphi, p662_1, u5elo1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h0, h635, hc34, hlam, hphi, ht45, p662_1, u5elo1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [hc05, hlam, hphi, p662_1, u5elo1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [hlam, p662_0]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [hc25, hlam, hphi, p662_1, u5elo1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h635, hc34, hlam, hphi, ht45, p662_1, u5elo1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h635, hc34, hlam, hphi, ht45, p662_1, u5elo1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h628, hlam, p662_1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h631, hlam, p662_1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [hlam, p662_0]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h631, h635, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p662_1, u2elo1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h631, h635, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p662_1, u2elo1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h629, hlam, p662_0]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [hc15, hlam, hphi, p662_1, u5elo3]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h633, hlam, p662_0]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [hlam, p662_0]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h635, hlam, p662_1]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h630, hlam, p662_0]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h632, hlam, p662_0]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h634, hlam, p662_0]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [h634, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p662_1, u2elo3]
                  · have p662_0 := h662c.1
                    have p662_1 := h662c.2.1
                    have p662_2 := h662c.2.2.1
                    have p662_3 := h662c.2.2.2
                    linarith only [hlam, p662_0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h688 | h688
                · linarith only [h633, h634, h688, hlam]
                · rcases h5bigk with h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [hlam, p690_0]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h0, hlam, p690_1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [hc25, hlam, hphi, p690_1, u5elo0]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h0, hc35, hlam, hphi, p690_1, u5elo1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h0, h634, hc24, hlam, hphi, ht45, p690_1, u5elo1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [hc05, hlam, hphi, p690_1, u5elo1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [hlam, p690_0]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h633, hc35, hlam, hphi, p690_1, u5elo1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h688, hc34, hlam, hphi, ht45, p690_1, u5elo1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h634, hc24, hlam, hphi, ht45, p690_1, u5elo1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h628, hlam, p690_1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h631, hlam, p690_1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [hlam, p690_0]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h688, hc34, hlam, hphi, ht45, p690_1, u5elo2]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h634, hlam, p690_1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h629, hlam, p690_0]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [hc15, hlam, hphi, p690_1, u5elo3]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h633, hlam, p690_0]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [hlam, p690_0]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h688, hlam, p690_1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h630, hlam, p690_0]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h632, hlam, p690_0]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h630, hc25, hlam, hphi, p690_1, u5elo0]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [h0, h630, hc35, hlam, hphi, p690_1, u5elo1]
                  · have p690_0 := h690c.1
                    have p690_1 := h690c.2.1
                    have p690_2 := h690c.2.2.1
                    have p690_3 := h690c.2.2.2
                    linarith only [hlam, p690_0]
            · linarith only [h629, h633, hc23, hlam, hphi, u3elo0]
          · linarith only [h0, h630, h632, hlam]
        · linarith only [h628, h631, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h719 | h719
        · rcases m.htr 1 4 5 (by decide) (by decide) with h720 | h720
          · rcases m.htr 2 3 5 (by decide) (by decide) with h721 | h721
            · rcases m.htr 2 4 5 (by decide) (by decide) with h722 | h722
              · linarith only [h628, h630, h722, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h724 | h724
                · linarith only [h628, h630, h721, h724, hlam]
                · rcases h5bigk with h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [hlam, p726_0]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h0, hlam, p726_1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h721, hc35, hlam, hphi, p726_1, u5elo0]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [hc35, hlam, hphi, p726_1, u5elo0]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h630, hlam, p726_1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [hc05, hlam, hphi, p726_1, u5elo1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [hlam, p726_0]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h721, hc35, hlam, hphi, p726_1, u5elo1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h724, hc34, hlam, hphi, ht45, p726_1, u5elo1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [hc45, hlam, hphi, p726_1, u5elo1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h628, hlam, p726_1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h719, hlam, p726_1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [hlam, p726_0]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h724, hc34, hlam, hphi, ht45, p726_1, u5elo2]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h722, hlam, p726_1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h629, hlam, p726_0]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h721, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p726_1, u2elo2]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h721, hlam, p726_0]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [hlam, p726_0]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h724, hlam, p726_1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p726_1, u5elo4]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h720, hlam, p726_0]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h720, h721, hc35, hlam, hphi, p726_1, u5elo1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [h720, hc35, hlam, hphi, p726_1, u5elo1]
                  · have p726_0 := h726c.1
                    have p726_1 := h726c.2.1
                    have p726_2 := h726c.2.2.1
                    have p726_3 := h726c.2.2.2
                    linarith only [hlam, p726_0]
            · linarith only [h629, h721, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h753 | h753
            · rcases m.htr 2 4 5 (by decide) (by decide) with h754 | h754
              · linarith only [h0, h720, h754, hc01, hlam, hphi, ht12, u2elo3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h756 | h756
                · linarith only [h0, h720, h756, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases h5bigk with h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [hlam, p758_0]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h0, hlam, p758_1]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h753, h756, hc34, hlam, hphi, ht45, p758_1, u5elo0]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h0, h756, hc34, hlam, hphi, ht45, p758_1, u5elo1]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h630, hlam, p758_1]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [hc05, hlam, hphi, p758_1, u5elo1]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [hlam, p758_0]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h753, h756, hc34, hlam, hphi, ht45, p758_1, u5elo1]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h720, h756, hc34, hlam, hphi, ht45, p758_1, u5elo4]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h720, hlam, p758_1]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h628, hlam, p758_1]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h719, hlam, p758_1]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [hlam, p758_0]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h756, hc34, hlam, hphi, ht45, p758_1, u5elo2]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h754, hlam, p758_1]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h629, hlam, p758_0]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [hc15, hlam, hphi, p758_1, u5elo3]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h753, hlam, p758_0]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [hlam, p758_0]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h756, hlam, p758_1]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [hc05, hlam, hphi, p758_1, u5elo4]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p758_1, u5elo4]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [hc25, hlam, hphi, p758_1, u5elo4]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [hc35, hlam, hphi, p758_1, u5elo4]
                  · have p758_0 := h758c.1
                    have p758_1 := h758c.2.1
                    have p758_2 := h758c.2.2.1
                    have p758_3 := h758c.2.2.2
                    linarith only [hlam, p758_0]
            · linarith only [h629, h753, hc23, hlam, hphi, u3elo0]
        · linarith only [h628, h719, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h786 | h786
      · rcases m.htr 1 2 5 (by decide) (by decide) with h787 | h787
        · rcases m.htr 1 4 5 (by decide) (by decide) with h788 | h788
          · rcases m.htr 2 3 5 (by decide) (by decide) with h789 | h789
            · linarith only [h629, h789, hc03, hlam, hphi, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h791 | h791
              · rcases m.htr 3 4 5 (by decide) (by decide) with h792 | h792
                · rcases h5bigk with h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hlam, p793_0]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h0, hlam, p793_1]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h791, hc45, hlam, hphi, p793_1, u5elo0]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h629, hlam, p793_1]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hc45, hlam, hphi, p793_1, u5elo0]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hc05, hlam, hphi, p793_1, u5elo1]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hlam, p793_0]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h791, hc45, hlam, hphi, p793_1, u5elo1]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hc35, hlam, hphi, p793_1, u5elo1]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hc45, hlam, hphi, p793_1, u5elo1]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h628, hlam, p793_1]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h787, hlam, p793_1]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hlam, p793_0]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h789, hlam, p793_1]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hc45, hlam, hphi, p793_1, u5elo2]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, p793_1, u3elo4]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hc15, hlam, hphi, p793_1, u5elo3]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hc25, hlam, hphi, p793_1, u5elo3]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hlam, p793_0]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hc45, hlam, hphi, p793_1, u5elo3]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h786, hlam, p793_0]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h788, hlam, p793_0]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h791, hlam, p793_0]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [h792, hlam, p793_0]
                  · have p793_0 := h793c.1
                    have p793_1 := h793c.2.1
                    have p793_2 := h793c.2.2.1
                    have p793_3 := h793c.2.2.2
                    linarith only [hlam, p793_0]
                · linarith only [h628, h629, h791, h792, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h820 | h820
                · rcases h5bigk with h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [hlam, p821_0]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h0, hlam, p821_1]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [hc25, hlam, hphi, p821_1, u5elo0]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h629, hlam, p821_1]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h0, h791, hc24, hlam, hphi, ht45, p821_1, u5elo1]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [hc05, hlam, hphi, p821_1, u5elo1]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [hlam, p821_0]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [hc25, hlam, hphi, p821_1, u5elo1]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [hc35, hlam, hphi, p821_1, u5elo1]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h791, hc24, hlam, hphi, ht45, p821_1, u5elo1]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h628, hlam, p821_1]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h787, hlam, p821_1]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [hlam, p821_0]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h789, hlam, p821_1]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h791, hlam, p821_1]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h786, h791, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p821_1, u3elo4]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [hc15, hlam, hphi, p821_1, u5elo3]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h789, hc23, hlam, hphi, ht34, ht45, p821_1, u5elo3]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [hlam, p821_0]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h791, hc24, hlam, hphi, ht45, p821_1, u5elo3]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h786, hlam, p821_0]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h788, hlam, p821_0]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h789, h820, hc23, hlam, hphi, p821_1, u3elo3]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [h820, hlam, p821_0]
                  · have p821_0 := h821c.1
                    have p821_1 := h821c.2.1
                    have p821_2 := h821c.2.2.1
                    have p821_3 := h821c.2.2.2
                    linarith only [hlam, p821_0]
                · linarith only [h629, h786, h820, hlam]
          · linarith only [h0, h786, h788, hlam]
        · linarith only [h628, h787, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h850 | h850
        · rcases m.htr 1 4 5 (by decide) (by decide) with h851 | h851
          · rcases m.htr 2 3 5 (by decide) (by decide) with h852 | h852
            · linarith only [h629, h852, hc03, hlam, hphi, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h854 | h854
              · linarith only [h628, h786, h854, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h856 | h856
                · rcases h5bigk with h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [hlam, p857_0]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h0, hlam, p857_1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h786, h856, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p857_1, u3elo3]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h629, hlam, p857_1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h786, hlam, p857_1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [hc05, hlam, hphi, p857_1, u5elo1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [hlam, p857_0]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [hc25, hlam, hphi, p857_1, u5elo1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h852, hc23, hlam, hphi, ht34, ht45, p857_1, u5elo1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h786, hc04, hlam, hphi, ht45, p857_1, u5elo1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h628, hlam, p857_1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h850, hlam, p857_1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [hlam, p857_0]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h852, hlam, p857_1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h854, hlam, p857_1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, p857_1, u3elo4]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [hc15, hlam, hphi, p857_1, u5elo3]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h852, hc23, hlam, hphi, ht34, ht45, p857_1, u5elo3]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [hlam, p857_0]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h786, hc04, hlam, hphi, ht45, p857_1, u5elo3]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h0, h851, hc01, hc14, hlam, hphi, p857_1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h851, hlam, p857_0]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h851, h852, hc23, hlam, hphi, ht34, ht45, p857_1, u5elo1]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [h856, hlam, p857_0]
                  · have p857_0 := h857c.1
                    have p857_1 := h857c.2.1
                    have p857_2 := h857c.2.2.1
                    have p857_3 := h857c.2.2.2
                    linarith only [hlam, p857_0]
                · rcases h5bigk with h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h0, hlam, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h852, hc23, hlam, hphi, ht34, ht45, p883_1, u5elo0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h629, hlam, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h786, hlam, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hc05, hlam, hphi, p883_1, u5elo1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h852, hc23, hlam, hphi, ht34, ht45, p883_1, u5elo1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hc35, hlam, hphi, p883_1, u5elo1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h856, hc34, hlam, hphi, ht45, p883_1, u5elo1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h628, hlam, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h850, hlam, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h852, hlam, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h854, hlam, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, p883_1, u3elo4]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hc15, hlam, hphi, p883_1, u5elo3]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h852, hc23, hlam, hphi, ht34, ht45, p883_1, u5elo3]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h856, hlam, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h0, h851, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p883_1, u5elo1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h851, hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h851, h852, hc23, hlam, hphi, ht34, ht45, p883_1, u5elo1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h851, hc35, hlam, hphi, p883_1, u5elo1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hlam, p883_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h909 | h909
            · linarith only [h629, h909, hc03, hlam, hphi, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h911 | h911
              · linarith only [h0, h851, h911, hc01, hlam, hphi, ht12, u2elo3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h913 | h913
                · linarith only [h0, h851, h913, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases h5bigk with h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [hlam, p915_0]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h0, hlam, p915_1]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h911, hc24, hlam, hphi, ht45, p915_1, u5elo0]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h629, hlam, p915_1]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h786, hlam, p915_1]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [hc05, hlam, hphi, p915_1, u5elo1]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [hlam, p915_0]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h851, h911, hc24, hlam, hphi, ht45, p915_1, u5elo4]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h629, h851, hc03, hlam, hphi, ht34, ht45, p915_1, u5elo4]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h851, hlam, p915_1]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h628, hlam, p915_1]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h850, hlam, p915_1]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [hlam, p915_0]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h909, hlam, p915_1]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h911, hlam, p915_1]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, p915_1, u3elo4]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h913, hc15, hlam, hphi, p915_1, u5elo4]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h909, h913, hc23, hlam, hphi, ht34, ht45, p915_1, u5elo4]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [hlam, p915_0]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h913, hlam, p915_1]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p915_1, u5elo4]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p915_1, u5elo4]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [h909, hc23, hlam, hphi, ht34, ht45, p915_1, u5elo4]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [hc35, hlam, hphi, p915_1, u5elo4]
                  · have p915_0 := h915c.1
                    have p915_1 := h915c.2.1
                    have p915_2 := h915c.2.2.1
                    have p915_3 := h915c.2.2.2
                    linarith only [hlam, p915_0]
        · linarith only [h628, h850, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h942 | h942
    · rcases m.htr 0 4 5 (by decide) (by decide) with h943 | h943
      · rcases m.htr 1 2 5 (by decide) (by decide) with h944 | h944
        · linarith only [h628, h944, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h946 | h946
          · rcases m.htr 2 3 5 (by decide) (by decide) with h947 | h947
            · rcases m.htr 2 4 5 (by decide) (by decide) with h948 | h948
              · rcases m.htr 3 4 5 (by decide) (by decide) with h949 | h949
                · rcases h5bigk with h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h0, hlam, p950_1]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h628, hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h949, hc45, hlam, hphi, p950_1, u5elo0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h0, hc45, hlam, hphi, p950_1, u5elo1]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [hc05, hlam, hphi, p950_1, u5elo1]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h944, hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h944, h949, hc45, hlam, hphi, p950_1, u5elo2]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h944, hc45, hlam, hphi, p950_1, u5elo2]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p950_1, u5elo2]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [hc15, hlam, hphi, p950_1, u5elo2]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h949, hc45, hlam, hphi, p950_1, u5elo2]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [hc45, hlam, hphi, p950_1, u5elo2]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h942, hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h0, h942, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p950_1, u0elo2]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h947, hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h942, hc45, hlam, hphi, p950_1, u5elo0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h943, hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h946, hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h948, hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [h949, hlam, p950_0]
                  · have p950_0 := h950c.1
                    have p950_1 := h950c.2.1
                    have p950_2 := h950c.2.2.1
                    have p950_3 := h950c.2.2.2
                    linarith only [hlam, p950_0]
                · rcases h5bigk with h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [hlam, p976_0]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h0, hlam, p976_1]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h628, hlam, p976_0]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h0, h944, hc35, hlam, hphi, p976_1, u5elo2]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h0, h944, h949, hc34, hlam, hphi, ht45, p976_1, u5elo2]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h944, hc05, hlam, hphi, p976_1, u5elo2]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [hlam, p976_0]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h944, hlam, p976_0]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h944, h949, hc34, hlam, hphi, ht45, p976_1, u5elo2]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h944, h949, hc34, hlam, hphi, ht45, p976_1, u5elo2]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h943, h949, hc34, hlam, hphi, ht45, p976_1, u5elo2]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [hc15, hlam, hphi, p976_1, u5elo2]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [hlam, p976_0]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h949, hc34, hlam, hphi, ht45, p976_1, u5elo2]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h949, hc34, hlam, hphi, ht45, p976_1, u5elo2]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h942, hlam, p976_0]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, p976_1, u3elo4]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h947, hlam, p976_0]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [hlam, p976_0]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h949, hlam, p976_1]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h943, hlam, p976_0]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h946, hlam, p976_0]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h948, hlam, p976_0]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [h948, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p976_1, u2elo3]
                  · have p976_0 := h976c.1
                    have p976_1 := h976c.2.1
                    have p976_2 := h976c.2.2.1
                    have p976_3 := h976c.2.2.2
                    linarith only [hlam, p976_0]
              · linarith only [h0, h943, h944, h948, hlam]
            · linarith only [h942, h947, hc23, hlam, hphi, u3elo0]
          · linarith only [h0, h943, h946, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1005 | h1005
        · linarith only [h1005, h628, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1007 | h1007
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1008 | h1008
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1009 | h1009
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1010 | h1010
                · linarith only [h1010, h942, h943, hlam]
                · rcases h5bigk with h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [hlam, p1012_0]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h0, hlam, p1012_1]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h628, hlam, p1012_0]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [hc35, hlam, hphi, p1012_1, u5elo0]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h943, hlam, p1012_1]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [hc05, hlam, hphi, p1012_1, u5elo1]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [hlam, p1012_0]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h1005, hlam, p1012_0]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h1005, h1010, hc34, hlam, hphi, ht45, p1012_1, u5elo2]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h1005, h943, hc04, hlam, hphi, ht45, p1012_1, u5elo2]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1012_1, u5elo2]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [hc15, hlam, hphi, p1012_1, u5elo2]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [hlam, p1012_0]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h1010, hc34, hlam, hphi, ht45, p1012_1, u5elo2]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h943, hc04, hlam, hphi, ht45, p1012_1, u5elo2]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h942, hlam, p1012_0]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1012_1, u3elo4]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h1008, hlam, p1012_0]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [hlam, p1012_0]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h1010, hlam, p1012_1]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1012_1, u5elo4]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h1007, hlam, p1012_0]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h1009, hlam, p1012_0]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [h1009, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1012_1, u2elo3]
                  · have p1012_0 := h1012c.1
                    have p1012_1 := h1012c.2.1
                    have p1012_2 := h1012c.2.2.1
                    have p1012_3 := h1012c.2.2.2
                    linarith only [hlam, p1012_0]
              · linarith only [h1005, h1007, h1009, hlam]
            · linarith only [h1008, h942, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1040 | h1040
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1041 | h1041
              · linarith only [h0, h1007, h1041, hc01, hlam, hphi, ht12, u2elo3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1043 | h1043
                · linarith only [h1005, h1041, h1043, hc12, hlam, hphi, ht23, u3elo3]
                · rcases h5bigk with h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [hlam, p1045_0]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h0, hlam, p1045_1]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h628, hlam, p1045_0]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [hc35, hlam, hphi, p1045_1, u5elo0]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h943, hlam, p1045_1]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [hc05, hlam, hphi, p1045_1, u5elo1]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [hlam, p1045_0]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h1005, hlam, p1045_0]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h1005, h1041, h1043, hc34, hlam, hphi, ht45, p1045_1, u5elo4]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h1007, hlam, p1045_1]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h0, h1041, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1045_1, u5elo4]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h1041, hc15, hlam, hphi, p1045_1, u5elo4]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [hlam, p1045_0]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h1041, h1043, hc34, hlam, hphi, ht45, p1045_1, u5elo4]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h1041, hlam, p1045_1]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h942, hlam, p1045_0]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1045_1, u3elo4]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h1040, hlam, p1045_0]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [hlam, p1045_0]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h1043, hlam, p1045_1]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1045_1, u5elo4]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1045_1, u5elo4]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [h1005, hc12, hlam, hphi, ht23, ht34, ht45, p1045_1, u5elo4]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [hc35, hlam, hphi, p1045_1, u5elo4]
                  · have p1045_0 := h1045c.1
                    have p1045_1 := h1045c.2.1
                    have p1045_2 := h1045c.2.2.1
                    have p1045_3 := h1045c.2.2.2
                    linarith only [hlam, p1045_0]
            · linarith only [h1040, h942, hc23, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1072 | h1072
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1073 | h1073
        · linarith only [h1073, h628, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1075 | h1075
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1076 | h1076
            · linarith only [h1076, h942, hc03, hlam, hphi, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1078 | h1078
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1079 | h1079
                · rcases h5bigk with h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [hlam, p1080_0]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h0, hlam, p1080_1]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h628, hlam, p1080_0]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h942, hlam, p1080_1]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [hc45, hlam, hphi, p1080_1, u5elo0]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1073, h1076, hc05, hlam, hphi, p1080_1, u5elo3]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [hlam, p1080_0]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1073, hlam, p1080_0]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1073, h1076, hlam, p1080_1]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1073, h1076, hc45, hlam, hphi, p1080_1, u5elo3]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h0, h1076, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1080_1, u5elo3]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1076, hc15, hlam, hphi, p1080_1, u5elo3]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [hlam, p1080_0]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1076, hlam, p1080_1]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1076, hc45, hlam, hphi, p1080_1, u5elo3]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1080_1, u5elo3]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1080_1, u5elo3]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1073, hc12, hlam, hphi, ht23, ht34, ht45, p1080_1, u5elo3]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [hlam, p1080_0]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [hc45, hlam, hphi, p1080_1, u5elo3]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1072, hlam, p1080_0]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1075, hlam, p1080_0]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1078, hlam, p1080_0]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [h1079, hlam, p1080_0]
                  · have p1080_0 := h1080c.1
                    have p1080_1 := h1080c.2.1
                    have p1080_2 := h1080c.2.2.1
                    have p1080_3 := h1080c.2.2.2
                    linarith only [hlam, p1080_0]
                · linarith only [h1072, h1079, h942, hlam]
              · linarith only [h0, h1072, h1073, h1078, hlam]
          · linarith only [h0, h1072, h1075, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1109 | h1109
        · linarith only [h1109, h628, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1111 | h1111
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1112 | h1112
            · linarith only [h1112, h942, hc03, hlam, hphi, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1114 | h1114
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1115 | h1115
                · rcases h5bigk with h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [hlam, p1116_0]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h0, hlam, p1116_1]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h628, hlam, p1116_0]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h942, hlam, p1116_1]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1072, hlam, p1116_1]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [hc05, hlam, hphi, p1116_1, u5elo1]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [hlam, p1116_0]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1109, hlam, p1116_0]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1109, h1112, hlam, p1116_1]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1072, h1109, h1112, hc04, hlam, hphi, ht45, p1116_1, u5elo3]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h0, h1112, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1116_1, u5elo3]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1112, hc15, hlam, hphi, p1116_1, u5elo3]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [hlam, p1116_0]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1112, hlam, p1116_1]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1072, h1112, hc04, hlam, hphi, ht45, p1116_1, u5elo3]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1116_1, u5elo3]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1116_1, u5elo3]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1109, hc12, hlam, hphi, ht23, ht34, ht45, p1116_1, u5elo3]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [hlam, p1116_0]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1072, hc04, hlam, hphi, ht45, p1116_1, u5elo3]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h0, h1111, hc01, hc14, hlam, hphi, p1116_1]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1111, hlam, p1116_0]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1114, hlam, p1116_0]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [h1115, hlam, p1116_0]
                  · have p1116_0 := h1116c.1
                    have p1116_1 := h1116c.2.1
                    have p1116_2 := h1116c.2.2.1
                    have p1116_3 := h1116c.2.2.2
                    linarith only [hlam, p1116_0]
                · linarith only [h0, h1109, h1112, h1114, h1115, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h1109, h1111, h1114, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1144 | h1144
            · linarith only [h1144, h942, hc03, hlam, hphi, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1146 | h1146
              · linarith only [h0, h1111, h1146, hc01, hlam, hphi, ht12, u2elo3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1148 | h1148
                · linarith only [h0, h1109, h1146, h1148, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases h5bigk with h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [hlam, p1150_0]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h0, hlam, p1150_1]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h628, hlam, p1150_0]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h942, hlam, p1150_1]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h1072, hlam, p1150_1]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h0, h1109, hc01, hlam, hphi, ht12, p1150_1, u2elo4]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [hlam, p1150_0]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h1109, hlam, p1150_0]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h1109, h1144, hlam, p1150_1]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h1111, hlam, p1150_1]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h0, h1144, h1148, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1150_1, u5elo4]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h1144, h1148, hc15, hlam, hphi, p1150_1, u5elo4]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [hlam, p1150_0]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h1144, hlam, p1150_1]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h1146, hlam, p1150_1]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h0, h1148, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1150_1, u5elo4]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h0, h1148, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1150_1, u5elo4]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h1148, hc25, hlam, hphi, p1150_1, u5elo4]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [hlam, p1150_0]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h1148, hlam, p1150_1]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1150_1, u5elo4]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1150_1, u5elo4]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h0, h1109, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1150_1, u5elo4]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [h1144, hc23, hlam, hphi, ht34, ht45, p1150_1, u5elo4]
                  · have p1150_0 := h1150c.1
                    have p1150_1 := h1150c.2.1
                    have p1150_2 := h1150c.2.2.1
                    have p1150_3 := h1150c.2.2.2
                    linarith only [hlam, p1150_0]

theorem r1l7_10_12_13_25_L_0_L_0_L_0_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_0_L_0_L_0_M_LI_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_0_L_0_L_0_M_LI_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
