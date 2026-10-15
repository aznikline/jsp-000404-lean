import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_68S9

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h437 | h437
  · rcases m.htr 0 4 5 (by decide) (by decide) with h438 | h438
    · rcases m.htr 1 2 3 (by decide) (by decide) with h439 | h439
      · rcases m.htr 1 2 4 (by decide) (by decide) with h440 | h440
        · rcases m.htr 1 3 4 (by decide) (by decide) with h441 | h441
          · linarith only [h1, h441, h6, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h443 | h443
            · rcases h0bigk with h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [hlam, p444_0]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h0, h439, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p444_1]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h437, hc01, hc35, hlam, hphi, ht0b, ht5b, p444_1]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h1, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p444_1, u1ehi2]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p444_1, u1ehi4]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h0, hlam, p444_0]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [hlam, p444_0]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p444_1, u1ehi2]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h0, h1, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p444_1, u1ehi2]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p444_1, u1ehi4]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h1, hlam, p444_1]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h4, hlam, p444_1]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [hlam, p444_0]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h6, hlam, p444_1]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h3, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p444_1, u1ehi4]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h2, hlam, p444_0]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h5, hlam, p444_0]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h1, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p444_1, u1ehi2]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [hlam, p444_0]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h3, h6, hc34, hlam, hphi, ht12, ht23, p444_1, u1ehi4]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h3, hlam, p444_0]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h0, h437, h440, h441, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p444_1, u1ehi2]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h437, hlam, p444_0]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [h438, hlam, p444_1]
              · have p444_0 := h444c.1
                have p444_1 := h444c.2.1
                have p444_2 := h444c.2.2.1
                have p444_3 := h444c.2.2.2
                linarith only [hlam, p444_0]
            · linarith only [h438, h441, h443, h6, hc34, hlam, hphi, ht12, ht23, u1ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h471 | h471
          · linarith only [h1, h471, h6, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h473 | h473
            · rcases h0bigk with h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [hlam, p474_0]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h0, h439, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p474_1, u1ehi2]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h3, h437, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p474_1, u1ehi4]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h439, h440, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p474_1, u1ehi2]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p474_1, u1ehi4]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h0, hlam, p474_0]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [hlam, p474_0]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h3, h437, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p474_1, u1ehi4]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h0, h439, h440, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p474_1, u1ehi2]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p474_1, u1ehi4]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h1, hlam, p474_1]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h4, hlam, p474_1]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [hlam, p474_0]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h6, hlam, p474_1]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h3, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p474_1, u1ehi4]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h2, hlam, p474_0]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h5, hlam, p474_0]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h1, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p474_1, u1ehi2]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [hlam, p474_0]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h3, h6, hc34, hlam, hphi, ht12, ht23, p474_1, u1ehi4]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h3, hlam, p474_0]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h0, h437, h439, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p474_1, u1ehi2]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h437, hlam, p474_0]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [h438, hlam, p474_1]
              · have p474_0 := h474c.1
                have p474_1 := h474c.2.1
                have p474_2 := h474c.2.2.1
                have p474_3 := h474c.2.2.2
                linarith only [hlam, p474_0]
            · linarith only [h438, h473, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
      · linarith only [h4, h439, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · linarith only [h437, h438, h6, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h503 | h503
    · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
      · rcases m.htr 1 2 4 (by decide) (by decide) with h505 | h505
        · rcases m.htr 1 3 4 (by decide) (by decide) with h506 | h506
          · linarith only [h1, h506, h6, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h508 | h508
            · rcases h0bigk with h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p509_1, u1ehi1]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p509_1, u1ehi2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h1, h437, h503, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p509_1, u1ehi2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h1, h437, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p509_1, u1ehi2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h0, hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p509_1, u1ehi2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h0, h1, h437, h503, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p509_1, u1ehi2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h0, h1, h437, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p509_1, u1ehi2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h1, hlam, p509_1]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h4, hlam, p509_1]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h6, hlam, p509_1]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h437, hlam, p509_1]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h2, hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h5, hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h1, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p509_1, u1ehi2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h1, h437, h6, hc34, hlam, hphi, ht12, ht23, p509_1, u1ehi2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h3, hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h0, h505, h506, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p509_1, u1ehi2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h1, h437, hc35, hlam, hphi, ht12, ht23, p509_1, u1ehi2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h503, hlam, p509_1]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [hlam, p509_0]
            · linarith only [h503, h506, h508, h6, hc34, hlam, hphi, ht12, ht23, u1ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h536 | h536
          · linarith only [h1, h5, h505, h536, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h538 | h538
            · rcases h0bigk with h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [hlam, p539_0]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h5, h504, h505, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi2]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi2]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h5, h504, h505, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi2]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi4]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h0, hlam, p539_0]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [hlam, p539_0]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi2]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h0, h5, h504, h505, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi2]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h0, h1, h437, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi2]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h1, hlam, p539_1]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h4, hlam, p539_1]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [hlam, p539_0]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h6, hlam, p539_1]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h437, hlam, p539_1]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h2, hlam, p539_0]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h5, hlam, p539_0]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h1, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi2]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [hlam, p539_0]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h1, h437, h6, hc34, hlam, hphi, ht12, ht23, p539_1, u1ehi2]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h3, hlam, p539_0]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h0, h504, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi2]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h1, h437, hc35, hlam, hphi, ht12, ht23, p539_1, u1ehi2]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [h503, hlam, p539_1]
              · have p539_0 := h539c.1
                have p539_1 := h539c.2.1
                have p539_2 := h539c.2.2.1
                have p539_3 := h539c.2.2.2
                linarith only [hlam, p539_0]
            · linarith only [h503, h504, h505, h538, h6, hc34, hlam, hphi, ht12, ht23, u1ehi2]
      · linarith only [h4, h504, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h567 | h567
      · rcases m.htr 1 2 4 (by decide) (by decide) with h568 | h568
        · rcases m.htr 1 3 4 (by decide) (by decide) with h569 | h569
          · linarith only [h1, h569, h6, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h571 | h571
            · linarith only [h2, h503, h571, hlam]
            · rcases h0bigk with h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h0, h567, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p573_1]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p573_1, u1ehi2]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p573_1, u1ehi3]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h3, h571, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p573_1, u1ehi3]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h0, hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p573_1, u1ehi2]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p573_1, u1ehi3]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h0, h1, h503, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p573_1, u1ehi2]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h1, hlam, p573_1]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h4, hlam, p573_1]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h6, hlam, p573_1]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h437, hlam, p573_1]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h2, hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h5, hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h1, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p573_1, u1ehi2]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h503, hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h3, hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h503, hc02, hc45, hlam, hphi, ht23, ht34, p573_1]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h1, h503, hc45, hlam, hphi, ht12, ht23, ht34, p573_1, u1ehi2]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h503, hc04, hc45, hlam, hphi, p573_1]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hlam, p573_0]
        · linarith only [h5, h503, h568, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
      · linarith only [h4, h567, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]

theorem r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x0_x0_x0 m hb0 hb1 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x0_x0_x1 m hb0 hb1 h0 h1 h2 h3 h4 h5 h6

theorem r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h601 | h601
  · linarith only [h4, h5, h601, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h603 | h603
    · rcases m.htr 0 4 5 (by decide) (by decide) with h604 | h604
      · rcases m.htr 1 2 3 (by decide) (by decide) with h605 | h605
        · rcases m.htr 1 2 4 (by decide) (by decide) with h606 | h606
          · linarith only [h0, h4, h5, h603, h606, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h608 | h608
            · linarith only [h3, h601, h603, h605, h608, hc12, hlam, hphi, u1ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h610 | h610
              · rcases h0bigk with h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h3, h4, h603, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p611_1, u1ehi4]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h3, h603, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p611_1, u1ehi4]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h3, h4, h5, h603, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p611_1, u1ehi4]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p611_1, u1ehi4]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h0, hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h3, h603, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p611_1, u1ehi4]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h5, hlam, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h3, h5, hc24, hlam, hphi, ht12, p611_1, u1ehi4]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h1, hlam, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h4, hlam, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h601, hlam, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h3, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p611_1, u1ehi4]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h2, hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h601, hc02, hc34, hlam, hphi, ht23, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h1, h601, hc34, hlam, hphi, ht12, ht23, p611_1, u1ehi2]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h3, h601, hc34, hlam, hphi, ht12, ht23, p611_1, u1ehi4]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h3, hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h4, h603, hlam, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h603, hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h604, hlam, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [hlam, p611_0]
              · linarith only [h601, h604, h610, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h4, h5, h605, hc12, hc24, hlam, hphi]
      · linarith only [h4, h5, h603, h604, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h640 | h640
      · rcases m.htr 1 2 3 (by decide) (by decide) with h641 | h641
        · rcases m.htr 1 2 4 (by decide) (by decide) with h642 | h642
          · linarith only [h0, h5, h642, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h644 | h644
            · linarith only [h1, h601, h644, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h646 | h646
              · rcases h0bigk with h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [hlam, p647_0]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h1, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p647_1, u1ehi2]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p647_1, u1ehi2]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h2, h641, h642, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p647_1, u1ehi2]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p647_1, u1ehi4]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h0, hlam, p647_0]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [hlam, p647_0]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p647_1, u1ehi2]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h5, hlam, p647_1]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h1, h603, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p647_1, u1ehi2]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h1, hlam, p647_1]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h4, hlam, p647_1]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [hlam, p647_0]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h601, hlam, p647_1]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h603, hlam, p647_1]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h2, hlam, p647_0]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h0, h641, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p647_1, u1ehi2]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h1, h601, hc34, hlam, hphi, ht12, ht23, p647_1, u1ehi2]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [hlam, p647_0]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h1, h601, h603, hc34, hlam, hphi, ht12, ht23, p647_1, u1ehi2]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h3, hlam, p647_0]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h0, h641, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p647_1, u1ehi2]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h1, h603, hc35, hlam, hphi, ht12, ht23, p647_1, u1ehi2]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [h640, hlam, p647_1]
                · have p647_0 := h647c.1
                  have p647_1 := h647c.2.1
                  have p647_2 := h647c.2.2.1
                  have p647_3 := h647c.2.2.2
                  linarith only [hlam, p647_0]
              · linarith only [h601, h640, h641, h642, h646, hc34, hlam, hphi, ht12, ht23, u1ehi2]
        · linarith only [h4, h5, h641, hc12, hc24, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h675 | h675
        · rcases m.htr 1 2 4 (by decide) (by decide) with h676 | h676
          · linarith only [h0, h5, h676, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h678 | h678
            · linarith only [h1, h601, h678, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h680 | h680
              · linarith only [h0, h5, h640, h680, hc14, hlam, hphi, u1ehi1]
              · rcases h0bigk with h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [hlam, p682_0]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h1, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p682_1, u1ehi2]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p682_1, u1ehi2]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h1, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p682_1, u1ehi2]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h3, h680, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p682_1, u1ehi3]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h0, hlam, p682_0]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [hlam, p682_0]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p682_1, u1ehi2]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h5, hlam, p682_1]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h5, h640, hlam, p682_1]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h1, hlam, p682_1]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h4, hlam, p682_1]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [hlam, p682_0]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h601, hlam, p682_1]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h603, hlam, p682_1]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h2, hlam, p682_0]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h640, hc02, hc45, hlam, hphi, ht23, ht34, p682_1]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h1, h640, hc45, hlam, hphi, ht12, ht23, ht34, p682_1, u1ehi2]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [hlam, p682_0]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h640, hlam, p682_0]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h3, hlam, p682_0]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h0, h675, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p682_1, u1ehi2]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h1, h603, hc35, hlam, hphi, ht12, ht23, p682_1, u1ehi2]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [h640, hc04, hc45, hlam, hphi, p682_1]
                · have p682_0 := h682c.1
                  have p682_1 := h682c.2.1
                  have p682_2 := h682c.2.2.1
                  have p682_3 := h682c.2.2.2
                  linarith only [hlam, p682_0]
        · linarith only [h4, h601, h675, hc34, hlam, hphi, ht12, ht23, u1ehi1]

theorem r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x0_x0 m hb0 hb1 h0 h1 h2 h3 h4 h5
  · exact r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x0_x1 m hb0 hb1 h0 h1 h2 h3 h4 h5

end R2N4
