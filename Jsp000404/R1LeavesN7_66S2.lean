import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_66S1

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_I_L_0_L_0_H_I_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
  · rcases m.htr 0 4 5 (by decide) (by decide) with h357 | h357
    · rcases m.htr 1 2 5 (by decide) (by decide) with h358 | h358
      · linarith only [h1, h358, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h360 | h360
        · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
          · rcases m.htr 1 4 5 (by decide) (by decide) with h362 | h362
            · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
              · rcases m.htr 2 3 5 (by decide) (by decide) with h364 | h364
                · rcases m.htr 2 4 5 (by decide) (by decide) with h365 | h365
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h366 | h366
                    · rcases h5bigk with h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h356, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p367_1, u3elo0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h1, hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h1, h365, h366, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p367_1, u2elo3]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h1, h365, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p367_1, u2elo3]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h0, hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h358, hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h0, h366, hc01, hc45, hlam, hphi, ht0b, ht5b, p367_1]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h0, h1, h365, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p367_1, u2elo3]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h365, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p367_1, u2elo3]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h365, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p367_1, u2elo3]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h363, h365, h366, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p367_1, u3elo2]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h363, h365, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p367_1, u3elo2]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h356, hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h361, hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h364, hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p367_1, u3elo4]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h357, hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h362, hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h365, hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [h366, hlam, p367_0]
                      · have p367_0 := h367c.1
                        have p367_1 := h367c.2.1
                        have p367_2 := h367c.2.2.1
                        have p367_3 := h367c.2.2.2
                        linarith only [hlam, p367_0]
                    · rcases h5bigk with h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h1, h362, h363, h365, h366, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p393_1, u3elo2]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h1, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h1, h363, h365, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p393_1, u3elo2]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h1, h363, h365, h366, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p393_1, u3elo2]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h0, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h358, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p393_1]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h0, h1, h363, h365, h366, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p393_1, u3elo2]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h363, h365, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p393_1, u3elo2]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h363, h365, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p393_1, u3elo2]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h363, h365, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p393_1, u3elo2]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h363, h365, h366, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p393_1, u3elo2]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h356, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h361, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h364, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h366, hlam, p393_1]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h357, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h362, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h365, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h360, h362, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p393_1]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hlam, p393_0]
                  · linarith only [h1, h360, h362, h365, hc02, hlam, hphi, ht23, u3elo1]
                · linarith only [h356, h364, hc23, hlam, hphi, u3elo0]
              · linarith only [h360, h363, hc23, hlam, hphi, u3elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h422 | h422
              · rcases m.htr 2 3 5 (by decide) (by decide) with h423 | h423
                · rcases m.htr 2 4 5 (by decide) (by decide) with h424 | h424
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h425 | h425
                    · linarith only [h360, h362, h425, hlam]
                    · rcases h5bigk with h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p427_1, u2elo4]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h1, hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h356, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p427_1, u3elo0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h356, h360, h362, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p427_1, u3elo0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h0, hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h358, hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p427_1]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h362, hlam, p427_1]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p427_1, u2elo4]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p427_1, u2elo4]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h423, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p427_1, u3elo2]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h360, h362, h422, h424, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p427_1, u3elo2]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h356, hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h361, hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h423, hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h425, hlam, p427_1]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h357, hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h358, hc12, hc45, hlam, hphi, ht23, ht34, p427_1]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h424, hlam, p427_0]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [h422, h424, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p427_1, u3elo2]
                      · have p427_0 := h427c.1
                        have p427_1 := h427c.2.1
                        have p427_2 := h427c.2.2.1
                        have p427_3 := h427c.2.2.2
                        linarith only [hlam, p427_0]
                  · linarith only [h1, h357, h424, hlam]
                · linarith only [h356, h423, hc23, hlam, hphi, u3elo0]
              · linarith only [h360, h422, hc23, hlam, hphi, u3elo1]
          · linarith only [h356, h361, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h457 | h457
          · rcases m.htr 1 4 5 (by decide) (by decide) with h458 | h458
            · rcases m.htr 2 3 4 (by decide) (by decide) with h459 | h459
              · linarith only [h360, h457, h459, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h461 | h461
                · linarith only [h1, h459, h461, hc02, hlam, hphi, ht23, u3elo3]
                · linarith only [h457, h461, hc23, hlam, hphi, u3elo1]
            · linarith only [h360, h457, h458, hlam]
          · linarith only [h356, h457, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h466 | h466
      · linarith only [h1, h466, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h468 | h468
        · rcases m.htr 1 3 5 (by decide) (by decide) with h469 | h469
          · rcases m.htr 1 4 5 (by decide) (by decide) with h470 | h470
            · linarith only [h0, h357, h470, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h472 | h472
              · rcases m.htr 2 3 5 (by decide) (by decide) with h473 | h473
                · rcases m.htr 2 4 5 (by decide) (by decide) with h474 | h474
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h475 | h475
                    · linarith only [h468, h470, h475, hlam]
                    · rcases h5bigk with h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [hlam, p477_0]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h357, h472, h474, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p477_1, u3elo2]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h1, hlam, p477_0]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h357, h472, h474, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p477_1, u3elo2]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h357, hlam, p477_1]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h0, hlam, p477_0]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [hlam, p477_0]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h466, hlam, p477_0]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p477_1]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h470, hlam, p477_1]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p477_1, u2elo4]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p477_1, u2elo4]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [hlam, p477_0]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h473, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p477_1, u3elo2]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h468, h470, h472, h474, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p477_1, u3elo2]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h356, hlam, p477_0]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h469, hlam, p477_0]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h473, hlam, p477_0]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [hlam, p477_0]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h475, hlam, p477_1]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h0, h466, hc12, hc45, hlam, hphi, ht23, ht34, p477_1]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h466, hc12, hc45, hlam, hphi, ht23, ht34, p477_1]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h474, hlam, p477_0]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [h472, h474, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p477_1, u3elo2]
                      · have p477_0 := h477c.1
                        have p477_1 := h477c.2.1
                        have p477_2 := h477c.2.2.1
                        have p477_3 := h477c.2.2.2
                        linarith only [hlam, p477_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h503 | h503
                    · linarith only [h357, h468, h503, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · rcases h5bigk with h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [hlam, p505_0]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h1, h466, hc12, hlam, hphi, p505_1, u2elo4]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h1, hlam, p505_0]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h356, h503, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p505_1, u3elo0]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h357, hlam, p505_1]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h0, hlam, p505_0]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [hlam, p505_0]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h466, hlam, p505_0]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h0, h503, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p505_1]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h470, hlam, p505_1]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p505_1, u2elo4]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p505_1, u2elo4]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [hlam, p505_0]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h473, h503, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p505_1, u3elo2]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h474, hlam, p505_1]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h356, hlam, p505_0]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h469, hlam, p505_0]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h473, hlam, p505_0]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [hlam, p505_0]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h503, hlam, p505_1]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h0, h466, hc12, hc45, hlam, hphi, ht23, ht34, p505_1]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h466, hc12, hc45, hlam, hphi, ht23, ht34, p505_1]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p505_1]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [h503, hc34, hc45, hlam, hphi, p505_1]
                      · have p505_0 := h505c.1
                        have p505_1 := h505c.2.1
                        have p505_2 := h505c.2.2.1
                        have p505_3 := h505c.2.2.2
                        linarith only [hlam, p505_0]
                · linarith only [h356, h473, hc23, hlam, hphi, u3elo0]
              · linarith only [h468, h472, hc23, hlam, hphi, u3elo1]
          · linarith only [h356, h469, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h534 | h534
          · rcases m.htr 1 4 5 (by decide) (by decide) with h535 | h535
            · linarith only [h0, h357, h535, hlam]
            · linarith only [h468, h534, h535, hlam]
          · linarith only [h356, h534, hc13, hlam, hphi, u3elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h539 | h539
    · rcases m.htr 1 2 5 (by decide) (by decide) with h540 | h540
      · linarith only [h1, h540, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h542 | h542
        · rcases m.htr 1 3 5 (by decide) (by decide) with h543 | h543
          · linarith only [h356, h543, hc03, hlam, hphi, u3elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h545 | h545
            · linarith only [h542, h543, h545, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h547 | h547
              · rcases m.htr 2 3 5 (by decide) (by decide) with h548 | h548
                · linarith only [h356, h548, hc03, hlam, hphi, u3elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h550 | h550
                  · linarith only [h540, h545, h547, h548, h550, hc12, hlam, hphi, ht23, u3elo4]
                  · linarith only [h1, h539, h550, hlam]
              · linarith only [h542, h547, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h554 | h554
          · linarith only [h1, h356, h542, h554, hc02, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h556 | h556
            · rcases m.htr 2 3 4 (by decide) (by decide) with h557 | h557
              · linarith only [h542, h557, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h559 | h559
                · linarith only [h554, h557, h559, hc13, hlam, hphi, u3elo3]
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
                        linarith only [h1, h540, h561, hc12, hlam, hphi, p563_1, u2elo3]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h1, hlam, p563_0]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h356, hlam, p563_1]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h1, h559, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p563_1, u3elo4]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h0, hlam, p563_0]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [hlam, p563_0]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h540, hlam, p563_0]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h554, hlam, p563_1]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p563_1]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h559, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p563_1, u3elo4]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h559, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p563_1, u3elo4]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [hlam, p563_0]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h559, hlam, p563_1]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h557, h561, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p563_1, u3elo3]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h0, h540, hc12, hlam, hphi, ht23, p563_1, u3elo4]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h540, hc12, hlam, hphi, ht23, p563_1, u3elo4]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p563_1, u3elo4]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [hlam, p563_0]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h562, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p563_1, u3elo3]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h539, hlam, p563_0]
                      · have p563_0 := h563c.1
                        have p563_1 := h563c.2.1
                        have p563_2 := h563c.2.2.1
                        have p563_3 := h563c.2.2.2
                        linarith only [h556, hlam, p563_0]
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
                    · linarith only [h356, h539, h542, h562, hc13, hlam, hphi, u3elo4]
                  · linarith only [h542, h556, h557, h561, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h591 | h591
              · linarith only [h542, h591, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h593 | h593
                · linarith only [h356, h591, h593, hc03, hlam, hphi, u3elo3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h595 | h595
                  · linarith only [h542, h556, h591, h595, hc13, hlam, hphi, u3elo3]
                  · linarith only [h1, h539, h595, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h598 | h598
      · linarith only [h1, h598, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h600 | h600
        · rcases m.htr 1 3 5 (by decide) (by decide) with h601 | h601
          · linarith only [h356, h601, hc03, hlam, hphi, u3elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h603 | h603
            · linarith only [h0, h539, h600, h601, h603, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h605 | h605
              · rcases m.htr 2 3 5 (by decide) (by decide) with h606 | h606
                · linarith only [h356, h606, hc03, hlam, hphi, u3elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h608 | h608
                  · linarith only [h0, h539, h601, h605, h606, h608, hc13, hlam, hphi, u3elo4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h610 | h610
                    · linarith only [h1, h608, h610, hc02, hlam, hphi, ht23, u3elo3]
                    · rcases h5bigk with h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [hlam, p612_0]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p612_1, u2elo4]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h1, hlam, p612_0]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h356, hlam, p612_1]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h539, hlam, p612_1]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h0, hlam, p612_0]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [hlam, p612_0]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h598, hlam, p612_0]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h601, hlam, p612_1]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h603, hlam, p612_1]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p612_1, u2elo4]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h606, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p612_1, u3elo4]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [hlam, p612_0]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h606, hlam, p612_1]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h608, hlam, p612_1]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h1, hc02, hlam, hphi, ht23, p612_1, u3elo4]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h598, hc12, hlam, hphi, ht23, p612_1, u3elo4]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p612_1, u3elo4]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [hlam, p612_0]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h610, hlam, p612_1]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h0, h598, hc12, hc45, hlam, hphi, ht23, ht34, p612_1]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h600, h601, hc34, hc45, hlam, hphi, p612_1]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p612_1]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [h606, hc23, hc45, hlam, hphi, ht34, p612_1]
                      · have p612_0 := h612c.1
                        have p612_1 := h612c.2.1
                        have p612_2 := h612c.2.2.1
                        have p612_3 := h612c.2.2.2
                        linarith only [hlam, p612_0]
              · linarith only [h600, h601, h605, hc23, hlam, hphi, u3elo4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h639 | h639
          · linarith only [h1, h356, h600, h639, hc02, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h641 | h641
            · linarith only [h0, h539, h641, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
              · linarith only [h600, h643, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h645 | h645
                · linarith only [h1, h356, h643, h645, hc02, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h647 | h647
                  · linarith only [h600, h641, h643, h647, hc13, hlam, hphi, u3elo3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h649 | h649
                    · linarith only [h1, h647, h649, hc02, hlam, hphi, ht23, u3elo3]
                    · rcases h5bigk with h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h1, h598, hc12, hlam, hphi, p651_1, u2elo4]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h1, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h356, hlam, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h539, hlam, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h0, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h598, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h639, hlam, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h641, hlam, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p651_1, u2elo4]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h598, h645, hc12, hlam, hphi, ht23, p651_1, u3elo4]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h645, hlam, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h647, hlam, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h0, h598, hc12, hlam, hphi, ht23, p651_1, u3elo4]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h598, hc12, hlam, hphi, ht23, p651_1, u3elo4]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p651_1, u3elo4]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h649, hlam, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h0, h598, hc12, hc45, hlam, hphi, ht23, ht34, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h598, hc12, hc45, hlam, hphi, ht23, ht34, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h356, hc03, hc45, hlam, hphi, ht34, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hlam, p651_0]

theorem r1l7_10_12_13_25_L_I_L_0_L_0_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_I_L_0_L_0_H_I_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_10_12_13_25_L_I_L_0_L_0_H_I_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
