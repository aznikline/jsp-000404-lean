import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h5 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h6 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 1 2 5 (by decide) (by decide) with h260 | h260
  · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
    · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
      · rcases m.htr 1 4 5 (by decide) (by decide) with h263 | h263
        · rcases m.htr 2 3 4 (by decide) (by decide) with h264 | h264
          · rcases m.htr 2 3 5 (by decide) (by decide) with h265 | h265
            · rcases m.htr 2 4 5 (by decide) (by decide) with h266 | h266
              · rcases m.htr 3 4 5 (by decide) (by decide) with h267 | h267
                · rcases h5bigk with h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p268_1, u1elo0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h0, h265, h267, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p268_1, u1elo0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h0, h267, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p268_1, u1elo0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p268_1, u1elo0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h1, hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h265, h267, hc45, hlam, hphi, ht01, ht0b, ht5b, p268_1, u1elo4]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h260, h267, hc45, hlam, hphi, ht01, ht0b, ht5b, p268_1, u1elo1]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h0, h2, h260, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p268_1, u1elo0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h3, hlam, p268_1]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h260, hlam, p268_1]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h267, h3, hc02, hc45, hlam, hphi, ht0b, ht5b, p268_1]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h0, h2, h260, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p268_1, u1elo0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h4, hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h262, hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h265, hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h4, hc03, hc45, hlam, hphi, ht0b, ht5b, p268_1]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h5, hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h263, hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h266, hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [h267, hlam, p268_0]
                  · have p268_0 := h268c.1
                    have p268_1 := h268c.2.1
                    have p268_2 := h268c.2.2.1
                    have p268_3 := h268c.2.2.2
                    linarith only [hlam, p268_0]
                · linarith only [h0, h263, h267, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h0, h263, h266, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h1, h262, h264, h265, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · linarith only [h260, h261, h264, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
        · linarith only [h0, h260, h263, h5, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
      · linarith only [h260, h261, h262, h6, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h300 | h300
      · rcases m.htr 1 4 5 (by decide) (by decide) with h301 | h301
        · rcases m.htr 2 3 4 (by decide) (by decide) with h302 | h302
          · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
            · rcases m.htr 2 4 5 (by decide) (by decide) with h304 | h304
              · rcases m.htr 3 4 5 (by decide) (by decide) with h305 | h305
                · rcases h5bigk with h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p306_1, u1elo0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h0, h303, h305, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p306_1, u1elo0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h0, h305, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p306_1, u1elo0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p306_1, u1elo0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h1, hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h303, h305, hc45, hlam, hphi, ht01, ht0b, ht5b, p306_1, u1elo4]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h300, h305, hc45, hlam, hphi, ht01, ht0b, ht5b, p306_1, u1elo2]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h260, hc45, hlam, hphi, ht01, ht0b, ht5b, p306_1, u1elo1]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h3, hlam, p306_1]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h260, hlam, p306_1]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h3, h305, hc02, hc45, hlam, hphi, ht0b, ht5b, p306_1]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h0, h2, h260, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p306_1, u1elo0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h4, hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h300, hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h303, hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h4, hc03, hc45, hlam, hphi, ht0b, ht5b, p306_1]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h5, hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h301, hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h304, hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [h305, hlam, p306_0]
                  · have p306_0 := h306c.1
                    have p306_1 := h306c.2.1
                    have p306_2 := h306c.2.2.1
                    have p306_3 := h306c.2.2.2
                    linarith only [hlam, p306_0]
                · linarith only [h0, h261, h305, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h301, h304, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h261, h300, h303, hc23, hc34, hlam, hphi]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h335 | h335
            · rcases m.htr 2 4 5 (by decide) (by decide) with h336 | h336
              · rcases m.htr 3 4 5 (by decide) (by decide) with h337 | h337
                · rcases h5bigk with h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p338_1, u1elo0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h0, h335, h337, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p338_1, u1elo0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h0, h337, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p338_1, u1elo0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p338_1, u1elo0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h1, hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h335, h337, hc45, hlam, hphi, ht01, ht0b, ht5b, p338_1, u1elo4]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h0, h2, h260, h337, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p338_1, u1elo0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h0, h2, h260, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p338_1, u1elo0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h3, hlam, p338_1]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h260, hlam, p338_1]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h3, h337, hc02, hc45, hlam, hphi, ht0b, ht5b, p338_1]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h0, h2, h260, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p338_1, u1elo0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h4, hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h300, hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h335, hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h335, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p338_1]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h5, hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h301, hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h336, hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [h337, hlam, p338_0]
                  · have p338_0 := h338c.1
                    have p338_1 := h338c.2.1
                    have p338_2 := h338c.2.2.1
                    have p338_3 := h338c.2.2.2
                    linarith only [hlam, p338_0]
                · linarith only [h0, h302, h337, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h301, h336, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h0, h261, h300, h335, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · linarith only [h0, h261, h300, h301, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h368 | h368
        · rcases m.htr 2 3 4 (by decide) (by decide) with h369 | h369
          · rcases m.htr 2 3 5 (by decide) (by decide) with h370 | h370
            · linarith only [h0, h260, h300, h370, h6, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h261, h368, h369, h370, h4, hc03, hc45, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h373 | h373
            · linarith only [h300, h369, h373, hc13, hc34, hlam, hphi]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h375 | h375
              · rcases m.htr 3 4 5 (by decide) (by decide) with h376 | h376
                · rcases h5bigk with h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [hlam, p377_0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p377_1, u1elo0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h0, h373, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p377_1, u1elo0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h0, h300, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p377_1, u1elo0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p377_1, u1elo0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h1, hlam, p377_0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [hlam, p377_0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h373, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p377_1, u1elo4]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h300, hlam, p377_1]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h260, hc45, hlam, hphi, ht01, ht0b, ht5b, p377_1, u1elo1]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h3, hlam, p377_1]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h260, hlam, p377_1]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [hlam, p377_0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h373, hlam, p377_1]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h0, h2, h260, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, p377_1, u1elo0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h4, hlam, p377_0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h4, hc03, hc15, hlam, hphi, ht0b, ht5b, p377_1]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h0, h373, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p377_1, u1elo0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [hlam, p377_0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h0, h4, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p377_1, u1elo0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h5, hlam, p377_0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h368, hlam, p377_0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h375, hlam, p377_0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [h376, hlam, p377_0]
                  · have p377_0 := h377c.1
                    have p377_1 := h377c.2.1
                    have p377_2 := h377c.2.2.1
                    have p377_3 := h377c.2.2.2
                    linarith only [hlam, p377_0]
                · linarith only [h0, h261, h376, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h1, h368, h375, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
        · linarith only [h0, h260, h368, h5, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
    · rcases m.htr 1 3 5 (by decide) (by decide) with h407 | h407
      · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
        · rcases m.htr 2 3 4 (by decide) (by decide) with h409 | h409
          · rcases m.htr 2 3 5 (by decide) (by decide) with h410 | h410
            · rcases m.htr 2 4 5 (by decide) (by decide) with h411 | h411
              · rcases m.htr 3 4 5 (by decide) (by decide) with h412 | h412
                · rcases h5bigk with h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h0, h260, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p413_1, u1elo0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h0, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p413_1, u1elo0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h0, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, p413_1, u1elo0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p413_1, u1elo0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h1, hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h260, hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p413_1, u1elo4]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h0, h408, hc45, hlam, hphi, ht01, ht0b, ht5b, p413_1, u1elo0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h3, hlam, p413_1]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p413_1]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h0, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, p413_1, u1elo0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h0, h3, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p413_1, u1elo0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h4, hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h407, hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h410, hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h4, hc03, hc45, hlam, hphi, ht0b, ht5b, p413_1]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h5, hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h408, hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h411, hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [h412, hlam, p413_0]
                  · have p413_0 := h413c.1
                    have p413_1 := h413c.2.1
                    have p413_2 := h413c.2.2.1
                    have p413_3 := h413c.2.2.2
                    linarith only [hlam, p413_0]
                · linarith only [h0, h408, h412, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h408, h411, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h407, h408, h409, h410, h6, hlam]
          · linarith only [h406, h409, h6, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h443 | h443
          · rcases m.htr 2 3 5 (by decide) (by decide) with h444 | h444
            · rcases m.htr 2 4 5 (by decide) (by decide) with h445 | h445
              · rcases m.htr 3 4 5 (by decide) (by decide) with h446 | h446
                · linarith only [h406, h408, h446, hlam]
                · rcases h5bigk with h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c | h448c
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [hlam, p448_0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p448_1, u1elo0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h0, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p448_1, u1elo0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h0, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, p448_1, u1elo0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h0, h408, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p448_1, u1elo0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h1, hlam, p448_0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [hlam, p448_0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h260, hlam, p448_0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p448_1, u1elo4]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h408, hlam, p448_1]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h3, hlam, p448_1]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p448_1]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [hlam, p448_0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h0, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, p448_1, u1elo0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h0, h3, h408, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p448_1, u1elo0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h4, hlam, p448_0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h407, hlam, p448_0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h444, hlam, p448_0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [hlam, p448_0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h446, hlam, p448_1]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h5, hlam, p448_0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h408, h6, hc12, hc45, hlam, hphi, ht23, ht34, p448_1]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h445, hlam, p448_0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [h0, h2, h445, hc35, hlam, hphi, ht01, ht0b, ht5b, p448_1, u1elo0]
                  · have p448_0 := h448c.1
                    have p448_1 := h448c.2.1
                    have p448_2 := h448c.2.2.1
                    have p448_3 := h448c.2.2.2
                    linarith only [hlam, p448_0]
              · linarith only [h0, h445, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h407, h443, h444, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
          · linarith only [h0, h406, h408, h443, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h477 | h477
        · linarith only [h406, h407, h477, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h479 | h479
          · rcases m.htr 2 3 5 (by decide) (by decide) with h480 | h480
            · rcases m.htr 2 4 5 (by decide) (by decide) with h481 | h481
              · rcases m.htr 3 4 5 (by decide) (by decide) with h482 | h482
                · linarith only [h0, h3, h406, h407, h477, h480, h482, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h406, h407, h482, h5, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h0, h481, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h486 | h486
              · linarith only [h477, h479, h480, h486, h6, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h0, h486, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · linarith only [h1, h406, h407, h479, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h490 | h490
      · rcases m.htr 1 4 5 (by decide) (by decide) with h491 | h491
        · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
          · rcases m.htr 2 3 5 (by decide) (by decide) with h493 | h493
            · rcases m.htr 2 4 5 (by decide) (by decide) with h494 | h494
              · rcases m.htr 3 4 5 (by decide) (by decide) with h495 | h495
                · rcases h5bigk with h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p496_1, u1elo0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h0, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p496_1, u1elo0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h0, h495, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p496_1, u1elo0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p496_1, u1elo0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h1, hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h260, hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h495, hc45, hlam, hphi, ht01, ht0b, ht5b, p496_1, u1elo4]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h490, hc45, hlam, hphi, ht01, ht0b, ht5b, p496_1, u1elo2]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h3, hlam, p496_1]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p496_1]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h0, h3, h495, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p496_1, u1elo0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h0, h3, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p496_1, u1elo0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h4, hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h490, hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h493, hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h4, hc03, hc45, hlam, hphi, ht0b, ht5b, p496_1]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h5, hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h491, hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h494, hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [h495, hlam, p496_0]
                  · have p496_0 := h496c.1
                    have p496_1 := h496c.2.1
                    have p496_2 := h496c.2.2.1
                    have p496_3 := h496c.2.2.2
                    linarith only [hlam, p496_0]
                · linarith only [h0, h406, h495, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h491, h494, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h406, h490, h493, hc23, hc34, hlam, hphi]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h525 | h525
            · rcases m.htr 2 4 5 (by decide) (by decide) with h526 | h526
              · rcases m.htr 3 4 5 (by decide) (by decide) with h527 | h527
                · rcases h5bigk with h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h0, h260, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p528_1, u1elo0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h0, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p528_1, u1elo0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h0, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, p528_1, u1elo0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p528_1, u1elo0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h1, hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h260, hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h527, hc45, hlam, hphi, ht01, ht0b, ht5b, p528_1, u1elo4]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p528_1, u1elo4]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h3, hlam, p528_1]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p528_1]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h492, h525, h527, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p528_1]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h0, h2, h492, h525, hc45, hlam, hphi, ht01, ht0b, ht5b, p528_1, u1elo0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h4, hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h490, hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h525, hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h4, hc03, hc45, hlam, hphi, ht0b, ht5b, p528_1]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h5, hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h491, hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h526, hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [h527, hlam, p528_0]
                  · have p528_0 := h528c.1
                    have p528_1 := h528c.2.1
                    have p528_2 := h528c.2.2.1
                    have p528_3 := h528c.2.2.2
                    linarith only [hlam, p528_0]
                · linarith only [h0, h406, h490, h5, h527, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h0, h491, h492, h526, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h406, h490, h525, hc23, hc34, hlam, hphi]
        · linarith only [h0, h406, h490, h491, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h558 | h558
        · rcases m.htr 2 3 4 (by decide) (by decide) with h559 | h559
          · rcases m.htr 2 3 5 (by decide) (by decide) with h560 | h560
            · rcases m.htr 2 4 5 (by decide) (by decide) with h561 | h561
              · rcases m.htr 3 4 5 (by decide) (by decide) with h562 | h562
                · rcases h5bigk with h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h0, h490, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p563_1, u1elo0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h0, h490, h5, h560, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p563_1, u1elo0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h0, h490, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p563_1, u1elo0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p563_1, u1elo0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h1, hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h260, hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h490, hlam, p563_1]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p563_1, u1elo4]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h3, hlam, p563_1]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p563_1]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h0, h3, h490, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p563_1, u1elo0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h0, h3, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p563_1, u1elo0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h4, hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h260, h562, hc12, hc34, hlam, hphi, ht23, p563_1]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h560, hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h0, h3, h5, h560, hc45, hlam, hphi, ht01, ht0b, ht5b, p563_1, u1elo0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h5, hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h558, hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h561, hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [h562, hlam, p563_0]
                  · have p563_0 := h563c.1
                    have p563_1 := h563c.2.1
                    have p563_2 := h563c.2.2.1
                    have p563_3 := h563c.2.2.2
                    linarith only [hlam, p563_0]
                · linarith only [h0, h558, h562, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h0, h558, h561, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h4, h406, h558, h559, h560, hc03, hc45, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h592 | h592
            · linarith only [h490, h559, h592, hc13, hc34, hlam, hphi]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h594 | h594
              · rcases m.htr 3 4 5 (by decide) (by decide) with h595 | h595
                · rcases h5bigk with h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [hlam, p596_0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h0, h260, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p596_1, u1elo0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h0, h260, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p596_1, u1elo0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h0, h260, h5, h592, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p596_1, u1elo0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p596_1, u1elo0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h1, hlam, p596_0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [hlam, p596_0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h260, hlam, p596_0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h490, hlam, p596_1]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p596_1, u1elo4]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h3, hlam, p596_1]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h2, h594, hc02, hc15, hlam, hphi, ht0b, ht5b, p596_1]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [hlam, p596_0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h592, hlam, p596_1]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h0, h4, h5, h592, hc45, hlam, hphi, ht01, ht0b, ht5b, p596_1, u1elo0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h4, hlam, p596_0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h0, h260, h4, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p596_1, u1elo0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h0, h4, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p596_1, u1elo0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [hlam, p596_0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h0, h4, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p596_1, u1elo0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h5, hlam, p596_0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h558, hlam, p596_0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h594, hlam, p596_0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [h595, hlam, p596_0]
                  · have p596_0 := h596c.1
                    have p596_1 := h596c.2.1
                    have p596_2 := h596c.2.2.1
                    have p596_3 := h596c.2.2.2
                    linarith only [hlam, p596_0]
                · linarith only [h0, h558, h595, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h558, h594, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
          · rcases m.htr 2 3 5 (by decide) (by decide) with h625 | h625
            · rcases m.htr 2 4 5 (by decide) (by decide) with h626 | h626
              · rcases m.htr 3 4 5 (by decide) (by decide) with h627 | h627
                · linarith only [h558, h6, h624, h627, hc12, hc23, hlam, hphi]
                · linarith only [h0, h406, h5, h627, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h5, h6, h626, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h406, h624, h625, hc13, hc35, hlam, hphi]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h632 | h632
            · linarith only [h490, h624, h632, hc13, hc34, hlam, hphi]
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
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p636_1, u1elo0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h0, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p636_1, u1elo0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h0, h5, h632, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p636_1, u1elo0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p636_1, u1elo0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h1, hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h260, hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h490, hlam, p636_1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h558, hlam, p636_1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h3, hlam, p636_1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht0b, ht5b, p636_1]
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
                    linarith only [h558, h6, hc12, hc25, hlam, hphi, p636_1]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h4, hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h0, h4, h5, h558, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p636_1, u1elo0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h0, h4, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p636_1, u1elo0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h0, h4, h5, h558, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p636_1, u1elo0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h5, hlam, p636_0]
                  · have p636_0 := h636c.1
                    have p636_1 := h636c.2.1
                    have p636_2 := h636c.2.2.1
                    have p636_3 := h636c.2.2.2
                    linarith only [h558, h6, h634, hc12, hc25, hlam, hphi, p636_1]
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
                · linarith only [h0, h2, h406, h634, h635, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h5, h6, h634, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]

set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h5 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_11_25_L_0_H_I_s1_x0_x0_x0_x0_x0 m hb1 hb5 hg0 hg1 h2 h3 h4 h5 h6
  · exact r1l7_11_25_L_0_H_I_s1_x0_x0_x0_x0_x1 m hb1 hb5 hg0 hg1 h2 h3 h4 h5 h6

end R2N4
