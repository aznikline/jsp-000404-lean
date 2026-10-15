import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S8
import Jsp000404.R1LeavesN7_6S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13584000 in
set_option maxHeartbeats 13584000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h5410 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h6326 | h6326
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6327 | h6327
    · linarith only [h0, h1, h6327, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6329 | h6329
      · linarith only [h0, h5410, h6329, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6331 | h6331
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6332 | h6332
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6333 | h6333
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6334 | h6334
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6335 | h6335
                · linarith only [h0, h5410, h6327, h6331, h6332, h6335, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6337 | h6337
                  · linarith only [h0, h5410, h6329, h6337, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6339 | h6339
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6340 | h6340
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6341 | h6341
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6342 | h6342
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6343 | h6343
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6344 | h6344
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6345 | h6345
                                · rcases h0bigk with h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c | h6346c
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [hlam, p6346_0]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h5410, h6335, h6340, hc02, hc23, hlam, hphi, p6346_1]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h1, hlam, p6346_0]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h5410, hlam, p6346_1]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    rcases p6346_3 (m.d 0 1) (by simp) with h6351 | h6351
                                    · rcases p6346_3 (m.d 0 2) (by simp) with h6352 | h6352
                                      · linarith only [h0, h6352, hlam]
                                      · linarith only [h6331, h6352, hlam]
                                    · linarith only [h6326, h6351, hlam]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h0, hlam, p6346_0]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [hlam, p6346_0]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h6327, hlam, p6346_0]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h6329, hlam, p6346_1]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    rcases p6346_3 (m.d 0 1) (by simp) with h6360 | h6360
                                    · rcases p6346_3 (m.d 0 2) (by simp) with h6361 | h6361
                                      · rcases p6346_3 (m.d 0 3) (by simp) with h6362 | h6362
                                        · rcases p6346_3 (m.d 0 4) (by simp) with h6363 | h6363
                                          · rcases p6346_3 (m.d 0 5) (by simp) with h6364 | h6364
                                            · linarith only [h6331, h6364, hlam]
                                            · rcases h0emin with h6366 | h6366 | h6366 | h6366 | h6366
                                              · rcases h2bigk with h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h0, h5410, h6335, h6340, hc12, hc23, hlam, hphi, p6367_1]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6327, hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6329, hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  rcases p6367_3 (m.d 0 2) (by simp) with h6372 | h6372
                                                  · rcases p6367_3 (m.d 1 2) (by simp) with h6373 | h6373
                                                    · linarith only [h0, h6373, hlam]
                                                    · linarith only [h6339, h6373, hlam]
                                                  · linarith only [h6372, hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h0, hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6335, hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6337, hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h0, h5410, h6335, h6340, h6343, h6345, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6367_1]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6326, h6339, h6343, h6345, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6346_1, p6367_1]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  rcases p6367_3 (m.d 0 2) (by simp) with h6383 | h6383
                                                  · linarith only [h6327, h6383, hlam]
                                                  · linarith only [h0, h6383, hlam]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h5410, h6337, h6366, hc23, hlam, ht01, ht12, p6367_1]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h0, h1, h6326, h6335, h6339, hlam, p6346_1, p6367_2]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6326, h6339, h6343, h6345, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6346_1, p6367_1]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  rcases p6367_3 (m.d 0 2) (by simp) with h6390 | h6390
                                                  · linarith only [h6329, h6390, hlam]
                                                  · linarith only [h0, h6390, hlam]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6342, hlam, p6367_1]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6326, h6329, h6339, hlam, p6346_1, p6367_2]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6331, hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6339, hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6343, hlam, p6367_1]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [h6344, hlam, p6367_0]
                                                · have p6367_0 := h6367c.1
                                                  have p6367_1 := h6367c.2.1
                                                  have p6367_2 := h6367c.2.2.1
                                                  have p6367_3 := h6367c.2.2.2
                                                  linarith only [hlam, p6367_0]
                                              · rcases h2bigk with h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c | h6401c
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h0, h5410, h6337, hc12, hc24, hlam, hphi, p6401_1]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6327, hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6329, hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  rcases p6401_3 (m.d 0 2) (by simp) with h6406 | h6406
                                                  · rcases p6401_3 (m.d 1 2) (by simp) with h6407 | h6407
                                                    · linarith only [h0, h6407, hlam]
                                                    · linarith only [h6339, h6407, hlam]
                                                  · linarith only [h6406, hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h0, hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6335, hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6337, hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h0, h5410, h6335, h6340, h6343, h6345, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6401_1]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6326, h6339, h6343, h6345, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6346_1, p6401_1]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  rcases p6401_3 (m.d 0 2) (by simp) with h6417 | h6417
                                                  · linarith only [h6327, h6417, hlam]
                                                  · linarith only [h0, h6417, hlam]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h5410, h6337, hc01, hc23, hlam, hphi, ht12, p6401_1]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h0, h5410, h6326, h6335, h6339, h6340, hlam, p6346_1, p6401_2]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6326, h6339, h6343, h6345, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6346_1, p6401_1]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  rcases p6401_3 (m.d 0 2) (by simp) with h6424 | h6424
                                                  · linarith only [h6329, h6424, hlam]
                                                  · linarith only [h0, h6424, hlam]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6342, hlam, p6401_1]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6326, h6329, h6339, hlam, p6346_1, p6401_2]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6331, hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6339, hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6343, hlam, p6401_1]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [h6344, hlam, p6401_0]
                                                · have p6401_0 := h6401c.1
                                                  have p6401_1 := h6401c.2.1
                                                  have p6401_2 := h6401c.2.2.1
                                                  have p6401_3 := h6401c.2.2.2
                                                  linarith only [hlam, p6401_0]
                                              · rcases h2bigk with h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h0, h6339, h6343, h6345, hc45, hlam, hphi, ht0b, ht5b, p6435_1, u0elo0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6327, hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6329, hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  rcases p6435_3 (m.d 0 2) (by simp) with h6440 | h6440
                                                  · rcases p6435_3 (m.d 1 2) (by simp) with h6441 | h6441
                                                    · linarith only [h0, h6441, hlam]
                                                    · linarith only [h6339, h6441, hlam]
                                                  · linarith only [h6440, hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h0, hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6335, hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6337, hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h0, h5410, h6335, h6340, h6343, h6345, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6435_1]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6326, h6339, h6343, h6345, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6346_1, p6435_1]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  rcases p6435_3 (m.d 0 2) (by simp) with h6451 | h6451
                                                  · linarith only [h6327, h6451, hlam]
                                                  · linarith only [h0, h6451, hlam]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6326, h6329, h6339, h6343, h6345, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6346_1, p6435_1]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h0, h5410, h6326, h6335, h6339, h6340, hlam, p6346_1, p6435_2]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p6346_1, p6435_1]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  rcases p6435_3 (m.d 0 2) (by simp) with h6458 | h6458
                                                  · linarith only [h6329, h6458, hlam]
                                                  · linarith only [h0, h6458, hlam]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6342, hlam, p6435_1]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6326, h6329, h6339, hlam, p6346_1, p6435_2]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6331, hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6339, hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6343, hlam, p6435_1]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [h6344, hlam, p6435_0]
                                                · have p6435_0 := h6435c.1
                                                  have p6435_1 := h6435c.2.1
                                                  have p6435_2 := h6435c.2.2.1
                                                  have p6435_3 := h6435c.2.2.2
                                                  linarith only [hlam, p6435_0]
                                              · rcases h2bigk with h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h0, h5410, h6335, h6340, hc12, hc23, hlam, hphi, p6469_1]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6327, hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6329, hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  rcases p6469_3 (m.d 0 2) (by simp) with h6474 | h6474
                                                  · rcases p6469_3 (m.d 1 2) (by simp) with h6475 | h6475
                                                    · linarith only [h0, h6475, hlam]
                                                    · linarith only [h6339, h6475, hlam]
                                                  · linarith only [h6474, hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h0, hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6335, hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6337, hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h0, h5410, h6335, h6340, h6343, h6345, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6469_1]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6326, h6339, h6343, h6345, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6346_1, p6469_1]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  rcases p6469_3 (m.d 0 2) (by simp) with h6485 | h6485
                                                  · linarith only [h6327, h6485, hlam]
                                                  · linarith only [h0, h6485, hlam]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h5410, h6337, hc01, hc23, hlam, hphi, ht12, p6469_1]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h0, h5410, h6326, h6335, h6339, h6340, hlam, p6346_1, p6469_2]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6326, h6339, h6343, h6345, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6346_1, p6469_1]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  rcases p6469_3 (m.d 0 2) (by simp) with h6492 | h6492
                                                  · linarith only [h6329, h6492, hlam]
                                                  · linarith only [h0, h6492, hlam]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6342, hlam, p6469_1]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6326, h6329, h6339, hlam, p6346_1, p6469_2]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6331, hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6339, hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6343, hlam, p6469_1]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [h6344, hlam, p6469_0]
                                                · have p6469_0 := h6469c.1
                                                  have p6469_1 := h6469c.2.1
                                                  have p6469_2 := h6469c.2.2.1
                                                  have p6469_3 := h6469c.2.2.2
                                                  linarith only [hlam, p6469_0]
                                              · linarith only [h0, h6366, hlam, p6346_1, u0elo0]
                                          · linarith only [h6334, h6363, hlam]
                                        · linarith only [h6333, h6362, hlam]
                                      · linarith only [h6331, h6361, hlam]
                                    · linarith only [h6326, h6360, hlam]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h0, h6339, h6343, h6345, hc45, hlam, hphi, ht0b, ht5b, p6346_1, u0elo2]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h0, h6339, h6343, h6345, hc45, hlam, hphi, ht0b, ht5b, p6346_1, u0elo2]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [hlam, p6346_0]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h0, h5410, h6339, h6343, h6345, hc45, hlam, hphi, ht0b, ht5b, p6346_1, u0elo2]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    rcases p6346_3 (m.d 0 1) (by simp) with h6512 | h6512
                                    · linarith only [h1, h6512, hlam]
                                    · linarith only [h6326, h6512, hlam]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h0, h6339, h6343, h6345, hc45, hlam, hphi, ht0b, ht5b, p6346_1, u0elo3]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h0, h6339, h6343, h6345, hc45, hlam, hphi, ht0b, ht5b, p6346_1, u0elo3]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h6332, hlam, p6346_0]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [hlam, p6346_0]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    rcases p6346_3 (m.d 0 1) (by simp) with h6519 | h6519
                                    · linarith only [h5410, h6519, hlam]
                                    · linarith only [h6326, h6519, hlam]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h6326, hlam, p6346_0]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h6331, hlam, p6346_1]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h6333, hlam, p6346_0]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [h6334, hlam, p6346_1]
                                  · have p6346_0 := h6346c.1
                                    have p6346_1 := h6346c.2.1
                                    have p6346_2 := h6346c.2.2.1
                                    have p6346_3 := h6346c.2.2.2
                                    linarith only [hlam, p6346_0]
                                · linarith only [h0, h5410, h6335, h6339, h6340, h6344, h6345, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h5410, h6326, h6337, h6341, h6344, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                            · linarith only [h0, h5410, h6335, h6339, h6340, h6343, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h5410, h6335, h6339, h6340, h6342, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h5410, h6339, h6341, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h0, h1, h6332, h6339, h6340, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h0, h1, h6331, h6335, h6339, hc12, hc23, hlam, hphi]
              · linarith only [h0, h5410, h6331, h6334, hlam]
            · linarith only [h0, h1, h6331, h6333, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6536 | h6536
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6537 | h6537
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6538 | h6538
                · linarith only [h0, h1, h6332, h6538, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6540 | h6540
                  · linarith only [h0, h1, h6329, h6332, h6540, hc02, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6542 | h6542
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6543 | h6543
                      · linarith only [h0, h1, h6332, h6538, h6542, h6543, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1, h6542, h6543, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h5410, h6331, h6540, h6542, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1, h6331, h6332, h6537, hlam]
            · linarith only [h0, h1, h6331, h6536, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6549 | h6549
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6550 | h6550
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6551 | h6551
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6552 | h6552
                · linarith only [h0, h6327, h6552, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6554 | h6554
                  · linarith only [h0, h6329, h6554, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6556 | h6556
                    · linarith only [h0, h6331, h6556, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6558 | h6558
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6559 | h6559
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6560 | h6560
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6561 | h6561
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6562 | h6562
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6563 | h6563
                                · rcases h0bigk with h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [hlam, p6564_0]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h5410, h6552, h6558, hc02, hc23, hlam, hphi, p6564_1]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h1, hlam, p6564_0]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h5410, hlam, p6564_1]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h0, h5410, h6331, h6552, h6558, hc12, hc23, hlam, hphi, p6564_1]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h0, hlam, p6564_0]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [hlam, p6564_0]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h6327, hlam, p6564_0]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h6329, hlam, p6564_1]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h6331, hlam, p6564_0]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6564_1, u0elo2]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    rcases p6564_3 (m.d 0 1) (by simp) with h6576 | h6576
                                    · linarith only [h1, h6576, hlam]
                                    · linarith only [h0, h6576, hlam]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [hlam, p6564_0]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h5410, h6326, h6556, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6564_1, u0elo2]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    rcases p6564_3 (m.d 0 1) (by simp) with h6581 | h6581
                                    · linarith only [h1, h6581, hlam]
                                    · linarith only [h6326, h6581, hlam]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h6326, h6556, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6564_1, u0elo3]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    rcases p6564_3 (m.d 0 1) (by simp) with h6585 | h6585
                                    · linarith only [h5410, h6585, hlam]
                                    · linarith only [h0, h6585, hlam]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h6549, hlam, p6564_0]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [hlam, p6564_0]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    rcases p6564_3 (m.d 0 1) (by simp) with h6590 | h6590
                                    · linarith only [h5410, h6590, hlam]
                                    · linarith only [h6326, h6590, hlam]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h6326, hlam, p6564_0]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h0, h1, h6326, h6552, hc12, hc23, hlam, hphi, p6564_1]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h6550, hlam, p6564_0]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [h6551, hlam, p6564_1]
                                  · have p6564_0 := h6564c.1
                                    have p6564_1 := h6564c.2.1
                                    have p6564_2 := h6564c.2.2.1
                                    have p6564_3 := h6564c.2.2.2
                                    linarith only [hlam, p6564_0]
                                · rcases h0bigk with h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c | h6598c
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [hlam, p6598_0]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h0, h5410, h6552, h6558, hc12, hc23, hlam, hphi, p6598_1]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h1, hlam, p6598_0]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h5410, hlam, p6598_1]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h5410, h6326, h6552, h6558, h6559, h6563, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6598_1]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h0, hlam, p6598_0]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [hlam, p6598_0]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h6327, hlam, p6598_0]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h6329, hlam, p6598_1]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h6331, hlam, p6598_0]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6598_1, u0elo2]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    rcases p6598_3 (m.d 0 1) (by simp) with h6610 | h6610
                                    · linarith only [h1, h6610, hlam]
                                    · linarith only [h0, h6610, hlam]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [hlam, p6598_0]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h5410, h6326, h6559, h6563, hc34, hlam, hphi, ht0b, ht45, ht5b, p6598_1, u0elo2]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h6326, h6559, h6563, hc34, hlam, hphi, ht0b, ht45, ht5b, p6598_1, u0elo2]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h6326, h6559, h6563, hc34, hlam, hphi, ht0b, ht45, ht5b, p6598_1, u0elo3]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    rcases p6598_3 (m.d 0 1) (by simp) with h6617 | h6617
                                    · linarith only [h5410, h6617, hlam]
                                    · linarith only [h0, h6617, hlam]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h6549, hlam, p6598_0]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [hlam, p6598_0]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h6326, h6549, h6559, h6563, hc34, hlam, hphi, ht0b, ht45, ht5b, p6598_1, u0elo2]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h6326, hlam, p6598_0]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h0, h5410, h6326, h6552, h6558, hc12, hc23, hlam, hphi, p6598_1]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h6550, hlam, p6598_0]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [h6551, hlam, p6598_1]
                                  · have p6598_0 := h6598c.1
                                    have p6598_1 := h6598c.2.1
                                    have p6598_2 := h6598c.2.2.1
                                    have p6598_3 := h6598c.2.2.2
                                    linarith only [hlam, p6598_0]
                              · linarith only [h5410, h6326, h6554, h6559, h6562, hlam]
                            · linarith only [h0, h5410, h6552, h6558, h6561, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h6326, h6552, h6556, h6560, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h5410, h6326, h6551, h6556, h6559, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h1, h6549, h6558, hlam]
              · linarith only [h5410, h6326, h6551, hlam]
            · linarith only [h1, h6326, h6550, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6635 | h6635
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6636 | h6636
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6637 | h6637
                · linarith only [h0, h1, h6549, h6637, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6639 | h6639
                  · linarith only [h0, h6329, h6639, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6641 | h6641
                    · linarith only [h0, h6331, h6641, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6643 | h6643
                      · linarith only [h1, h6326, h6549, h6637, h6641, h6643, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h6326, h6641, h6643, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h6326, h6549, h6636, hlam]
            · linarith only [h1, h6326, h6635, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6648 | h6648
    · linarith only [h0, h1, h6648, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6650 | h6650
      · linarith only [h0, h5410, h6650, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6652 | h6652
        · linarith only [h0, h6326, h6652, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6654 | h6654
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6655 | h6655
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6656 | h6656
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6657 | h6657
                · linarith only [h0, h6326, h6648, h6654, h6656, h6657, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6659 | h6659
                  · linarith only [h0, h6326, h6650, h6656, h6659, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6661 | h6661
                    · linarith only [h0, h6652, h6661, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6663 | h6663
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6664 | h6664
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6665 | h6665
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6666 | h6666
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6667 | h6667
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6668 | h6668
                                · rcases h0bigk with h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, h6326, h6657, h6663, h6664, hc12, hc23, hlam, hphi, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h1, hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h5410, hlam, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6326, hlam, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6648, hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6650, hlam, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6652, hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6669_1, u0elo2]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    rcases p6669_3 (m.d 0 1) (by simp) with h6681 | h6681
                                    · linarith only [h1, h6681, hlam]
                                    · linarith only [h0, h6681, hlam]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, h5410, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6669_1, u0elo2]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, h6326, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6669_1, u0elo2]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6669_1, u0elo3]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    rcases p6669_3 (m.d 0 1) (by simp) with h6688 | h6688
                                    · linarith only [h5410, h6688, hlam]
                                    · linarith only [h0, h6688, hlam]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6654, hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, h6326, h6654, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6669_1, u0elo2]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6669_1, u0elo4]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    rcases p6669_3 (m.d 0 1) (by simp) with h6695 | h6695
                                    · linarith only [h6326, h6695, hlam]
                                    · linarith only [h0, h6695, hlam]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6655, hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6656, hlam, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [hlam, p6669_0]
                                · rcases h0bigk with h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [hlam, p6701_0]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h0, h1, h6657, hc12, hc23, hlam, hphi, p6701_1]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h1, hlam, p6701_0]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h5410, hlam, p6701_1]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h6326, hlam, p6701_1]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h0, hlam, p6701_0]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [hlam, p6701_0]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h6648, hlam, p6701_0]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h6650, hlam, p6701_1]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h6652, hlam, p6701_0]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6701_1, u0elo2]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    rcases p6701_3 (m.d 0 1) (by simp) with h6713 | h6713
                                    · linarith only [h1, h6713, hlam]
                                    · linarith only [h0, h6713, hlam]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [hlam, p6701_0]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h6656, h6668, hc34, hlam, hphi, ht0b, ht45, ht5b, p6701_1, u0elo2]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h0, h6326, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6701_1, u0elo2]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6701_1, u0elo3]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    rcases p6701_3 (m.d 0 1) (by simp) with h6720 | h6720
                                    · linarith only [h5410, h6720, hlam]
                                    · linarith only [h0, h6720, hlam]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h6654, hlam, p6701_0]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [hlam, p6701_0]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h0, h6326, h6654, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6701_1, u0elo2]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6701_1, u0elo4]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    rcases p6701_3 (m.d 0 1) (by simp) with h6727 | h6727
                                    · linarith only [h6326, h6727, hlam]
                                    · linarith only [h0, h6727, hlam]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h6655, hlam, p6701_0]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [h6656, hlam, p6701_1]
                                  · have p6701_0 := h6701c.1
                                    have p6701_1 := h6701c.2.1
                                    have p6701_2 := h6701c.2.2.1
                                    have p6701_3 := h6701c.2.2.2
                                    linarith only [hlam, p6701_0]
                              · linarith only [h6650, h6656, h6667, hlam]
                            · linarith only [h0, h1, h6657, h6666, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h6657, h6665, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h5410, h6654, h6656, h6664, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1, h6654, h6663, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6738 | h6738
                · linarith only [h0, h5410, h6656, h6738, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6740 | h6740
                  · linarith only [h0, h5410, h6656, h6740, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6742 | h6742
                    · linarith only [h0, h6652, h6742, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6744 | h6744
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6745 | h6745
                        · linarith only [h0, h5410, h6656, h6740, h6745, hc12, hc24, hlam, hphi]
                        · linarith only [h0, h5410, h6745, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h0, h1, h6654, h6744, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6749 | h6749
              · linarith only [h6654, h6655, h6749, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6751 | h6751
                · linarith only [h0, h1, h6655, h6751, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6753 | h6753
                  · linarith only [h0, h5410, h6749, h6753, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6755 | h6755
                    · linarith only [h0, h6652, h6755, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6757 | h6757
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6758 | h6758
                        · linarith only [h0, h5410, h6749, h6751, h6757, h6758, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h5410, h6758, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h6654, h6655, h6757, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6762 | h6762
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6763 | h6763
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6764 | h6764
                · linarith only [h0, h6326, h6654, h6762, h6764, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6766 | h6766
                  · linarith only [h0, h6650, h6766, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6768 | h6768
                    · linarith only [h0, h6652, h6768, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6770 | h6770
                      · linarith only [h0, h6326, h6654, h6762, h6764, h6770, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h6770, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h6654, h6762, h6763, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6774 | h6774
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6775 | h6775
                · linarith only [h0, h1, h6762, h6775, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6777 | h6777
                  · linarith only [h0, h6650, h6777, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6779 | h6779
                    · linarith only [h0, h6652, h6779, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6781 | h6781
                      · linarith only [h0, h1, h6654, h6775, h6781, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h6781, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6784 | h6784
                · linarith only [h0, h1, h6762, h6784, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6786 | h6786
                  · linarith only [h0, h5410, h6774, h6786, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6788 | h6788
                    · linarith only [h0, h1, h6652, h6654, h6774, h6788, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6790 | h6790
                      · linarith only [h0, h1, h6654, h6784, h6790, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h6790, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 13584000 in
set_option maxHeartbeats 13584000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h5410 | h5410
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0 m hb0 hb2 hb4 hg0 h1 h5410
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x1 m hb0 hb2 hb4 hg0 h1 h5410

set_option maxHeartbeats 13584000 in
set_option maxHeartbeats 13584000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s0_x0 m hb0 hb2 hb4 hg0 h1
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s0_x1 m hb0 hb2 hb4 hg0 h1

end R2N4
