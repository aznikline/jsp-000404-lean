import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_44S11
import Jsp000404.R1LeavesN7_44S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1328 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2328 | h2328
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2329 | h2329
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2330 | h2330
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2331 | h2331
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2332 | h2332
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2333 | h2333
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2334 | h2334
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2335 | h2335
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2336 | h2336
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2337 | h2337
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2338 | h2338
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2339 | h2339
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2340 | h2340
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2341 | h2341
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2342 | h2342
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2343 | h2343
                                · rcases h2bigk with h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h0, hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2340, h2343, hc02, hc45, hlam, hphi, ht0b, ht5b, p2344_1]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h0, h2340, h2343, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2344_1]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    rcases p2344_3 (m.d 0 2) (by simp) with h2349 | h2349
                                    · rcases p2344_3 (m.d 1 2) (by simp) with h2350 | h2350
                                      · rcases p2344_3 (m.d 2 3) (by simp) with h2351 | h2351
                                        · linarith only [h2328, h2351, hlam]
                                        · linarith only [h2341, h2351, hlam]
                                      · linarith only [h2336, h2350, hlam]
                                    · linarith only [h2349, hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2344_1]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2340, h2343, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2344_1]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2340, h2343, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2344_1]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    rcases p2344_3 (m.d 0 2) (by simp) with h2360 | h2360
                                    · linarith only [h0, h2360, hlam]
                                    · linarith only [h2330, h2360, hlam]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2328, hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2334, hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2328, h2340, h2343, hc02, hc45, hlam, hphi, ht0b, ht5b, p2344_1]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h1328, h2328, h2341, h2343, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2344_1, u3elo1]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2329, hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2335, hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2340, hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h0, h2329, h2341, h2343, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2344_1]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2330, hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2336, hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2341, hlam, p2344_0]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [h2342, hlam, p2344_1]
                                  · have p2344_0 := h2344c.1
                                    have p2344_1 := h2344c.2.1
                                    have p2344_2 := h2344c.2.2.1
                                    have p2344_3 := h2344c.2.2.2
                                    linarith only [hlam, p2344_0]
                                · rcases h2bigk with h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c | h2378c
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h0, hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h0, h2340, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2378_1]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h0, h2342, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2378_1]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h0, h2342, h2343, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2378_1]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2378_1]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2340, h2342, h2343, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2378_1]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2342, h2343, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2378_1]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2342, h2343, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2378_1]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2328, hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2334, hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2328, h2342, h2343, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2378_1]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h1328, h2328, h2342, h2343, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2378_1, u3elo1]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2329, hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2335, hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2340, hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2342, h2343, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2378_1]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2330, hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2336, hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2341, hlam, p2378_0]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [h2342, hlam, p2378_1]
                                  · have p2378_0 := h2378c.1
                                    have p2378_1 := h2378c.2.1
                                    have p2378_2 := h2378c.2.2.1
                                    have p2378_3 := h2378c.2.2.2
                                    linarith only [hlam, p2378_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2404 | h2404
                                · linarith only [h1328, h2331, h2342, h2404, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · rcases h2bigk with h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h0, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h0, h2340, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2406_1]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    rcases p2406_3 (m.d 0 2) (by simp) with h2410 | h2410
                                    · rcases p2406_3 (m.d 1 2) (by simp) with h2411 | h2411
                                      · rcases p2406_3 (m.d 2 3) (by simp) with h2412 | h2412
                                        · linarith only [h2328, h2412, hlam]
                                        · linarith only [h2340, h2412, hlam]
                                      · linarith only [h2335, h2411, hlam]
                                    · linarith only [h2410, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    rcases p2406_3 (m.d 0 2) (by simp) with h2417 | h2417
                                    · rcases p2406_3 (m.d 1 2) (by simp) with h2418 | h2418
                                      · rcases p2406_3 (m.d 2 3) (by simp) with h2419 | h2419
                                        · linarith only [h2328, h2419, hlam]
                                        · linarith only [h2341, h2419, hlam]
                                      · linarith only [h2336, h2418, hlam]
                                    · linarith only [h2417, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2406_1]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2341, h2404, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2406_1]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    rcases p2406_3 (m.d 0 2) (by simp) with h2427 | h2427
                                    · linarith only [h0, h2427, hlam]
                                    · linarith only [h2329, h2427, hlam]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    rcases p2406_3 (m.d 0 2) (by simp) with h2430 | h2430
                                    · linarith only [h0, h2430, hlam]
                                    · linarith only [h2330, h2430, hlam]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2328, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2334, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2340, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2406_1, u3elo2]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h1328, h2328, h2341, h2404, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2406_1, u3elo1]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2329, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2335, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2340, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2342, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2330, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2336, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2341, hlam, p2406_0]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [h2330, h2340, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2406_1]
                                  · have p2406_0 := h2406c.1
                                    have p2406_1 := h2406c.2.1
                                    have p2406_2 := h2406c.2.2.1
                                    have p2406_3 := h2406c.2.2.2
                                    linarith only [hlam, p2406_0]
                            · linarith only [h1328, h2332, h2341, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1328, h2331, h2340, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1328, h1975, h2331, h2333, h2339, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h1328, h2332, h2338, hlam]
                    · linarith only [h1328, h2337, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2330, h2331, h2333, h2336, hc01, hlam, hphi, ht12, ht23, u3elo0]
                · linarith only [h0, h2329, h2335, hlam]
              · linarith only [h0, h2334, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2456 | h2456
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2457 | h2457
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2458 | h2458
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2459 | h2459
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2460 | h2460
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2461 | h2461
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2462 | h2462
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2463 | h2463
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2464 | h2464
                              · linarith only [h2329, h2333, h2464, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2466 | h2466
                                · linarith only [h2328, h2333, h2462, h2466, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases h2bigk with h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c | h2468c
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h0, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2463, h2466, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2468_1]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    rcases p2468_3 (m.d 0 2) (by simp) with h2472 | h2472
                                    · rcases p2468_3 (m.d 1 2) (by simp) with h2473 | h2473
                                      · rcases p2468_3 (m.d 2 3) (by simp) with h2474 | h2474
                                        · linarith only [h2328, h2474, hlam]
                                        · linarith only [h2462, h2474, hlam]
                                      · linarith only [h2457, h2473, hlam]
                                    · linarith only [h2472, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    rcases p2468_3 (m.d 0 2) (by simp) with h2479 | h2479
                                    · rcases p2468_3 (m.d 1 2) (by simp) with h2480 | h2480
                                      · rcases p2468_3 (m.d 2 3) (by simp) with h2481 | h2481
                                        · linarith only [h2328, h2481, hlam]
                                        · linarith only [h2463, h2481, hlam]
                                      · linarith only [h2458, h2480, hlam]
                                    · linarith only [h2479, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2468_1]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2463, h2466, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2468_1]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    rcases p2468_3 (m.d 0 2) (by simp) with h2489 | h2489
                                    · linarith only [h0, h2489, hlam]
                                    · linarith only [h2329, h2489, hlam]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    rcases p2468_3 (m.d 0 2) (by simp) with h2492 | h2492
                                    · linarith only [h0, h2492, hlam]
                                    · linarith only [h2330, h2492, hlam]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2328, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2456, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2328, h2462, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2468_1]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h1328, h2328, h2463, h2466, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2468_1, u3elo1]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2329, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2457, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2462, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2464, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2330, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2458, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h2463, hlam, p2468_0]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [h0, h2330, h2462, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2468_1]
                                  · have p2468_0 := h2468c.1
                                    have p2468_1 := h2468c.2.1
                                    have p2468_2 := h2468c.2.2.1
                                    have p2468_3 := h2468c.2.2.2
                                    linarith only [hlam, p2468_0]
                            · linarith only [h1328, h2332, h2463, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1328, h2331, h2462, hc23, hlam, hphi, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2512 | h2512
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2513 | h2513
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2514 | h2514
                              · linarith only [h2329, h2333, h2514, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2516 | h2516
                                · linarith only [h1975, h2461, h2512, h2516, hc01, hc23, hlam, hphi, ht12]
                                · rcases h2bigk with h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h0, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h0, h2513, h2516, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2518_1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    rcases p2518_3 (m.d 0 2) (by simp) with h2522 | h2522
                                    · rcases p2518_3 (m.d 1 2) (by simp) with h2523 | h2523
                                      · rcases p2518_3 (m.d 2 3) (by simp) with h2524 | h2524
                                        · linarith only [h2328, h2524, hlam]
                                        · linarith only [h2512, h2524, hlam]
                                      · linarith only [h2457, h2523, hlam]
                                    · linarith only [h2522, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    rcases p2518_3 (m.d 0 2) (by simp) with h2529 | h2529
                                    · rcases p2518_3 (m.d 1 2) (by simp) with h2530 | h2530
                                      · rcases p2518_3 (m.d 2 3) (by simp) with h2531 | h2531
                                        · linarith only [h2328, h2531, hlam]
                                        · linarith only [h2513, h2531, hlam]
                                      · linarith only [h2458, h2530, hlam]
                                    · linarith only [h2529, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2518_1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2513, h2516, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2518_1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    rcases p2518_3 (m.d 0 2) (by simp) with h2539 | h2539
                                    · linarith only [h0, h2539, hlam]
                                    · linarith only [h2329, h2539, hlam]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    rcases p2518_3 (m.d 0 2) (by simp) with h2542 | h2542
                                    · linarith only [h0, h2542, hlam]
                                    · linarith only [h2330, h2542, hlam]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2328, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2456, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2512, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2518_1, u3elo2]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h1328, h2328, h2512, h2514, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2518_1, u3elo1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2329, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2457, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2512, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2514, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2330, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2458, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2513, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2330, h2512, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2518_1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [hlam, p2518_0]
                            · linarith only [h1328, h2332, h2513, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1328, h2331, h2512, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1328, h2332, h2460, hlam]
                    · linarith only [h1328, h2459, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1328, h2330, h2332, h2458, hc01, hlam, hphi, ht12, ht23, u3elo1]
                · linarith only [h0, h2329, h2457, hlam]
              · linarith only [h0, h2456, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2567 | h2567
            · linarith only [h2331, h2332, h2567, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2569 | h2569
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2570 | h2570
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2571 | h2571
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2572 | h2572
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2573 | h2573
                      · linarith only [h2332, h2573, hc03, hlam, hphi, u3elo1]
                      · linarith only [h1328, h2573, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h1328, h2572, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2330, h2571, hlam]
                · linarith only [h0, h2329, h2331, h2332, h2570, hc02, hlam, hphi, ht23, u3elo4]
              · linarith only [h0, h2569, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2580 | h2580
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2581 | h2581
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2582 | h2582
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2583 | h2583
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2584 | h2584
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2585 | h2585
                    · linarith only [h2331, h2585, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1328, h2585, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2330, h2584, hlam]
                · linarith only [h0, h2329, h2331, h2583, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h2582, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2331, h2580, h2581, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2592 | h2592
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2593 | h2593
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2594 | h2594
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2595 | h2595
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2596 | h2596
                    · linarith only [h2331, h2596, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1328, h2596, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2330, h2595, hlam]
                · linarith only [h0, h2329, h2594, hlam]
              · linarith only [h0, h2593, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2602 | h2602
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2603 | h2603
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2604 | h2604
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2605 | h2605
                    · linarith only [h1328, h2331, h2605, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1328, h2605, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2330, h2604, hlam]
                · linarith only [h0, h2329, h2603, hlam]
              · linarith only [h0, h2602, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2611 | h2611
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2612 | h2612
          · linarith only [h2328, h2330, h2612, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2614 | h2614
            · linarith only [h2329, h2330, h2614, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2616 | h2616
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2617 | h2617
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2618 | h2618
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2619 | h2619
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2620 | h2620
                      · linarith only [h2612, h2620, hc03, hlam, hphi, u3elo1]
                      · linarith only [h1328, h2620, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h1328, h2619, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2624 | h2624
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2625 | h2625
                      · linarith only [h2612, h2625, hc03, hlam, hphi, u3elo1]
                      · linarith only [h1328, h2625, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h1328, h2624, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h2329, h2617, hlam]
              · linarith only [h0, h2616, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2631 | h2631
          · linarith only [h2328, h2330, h2611, h2631, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2633 | h2633
            · linarith only [h2329, h2330, h2633, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2635 | h2635
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2636 | h2636
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2637 | h2637
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2638 | h2638
                    · linarith only [h2611, h2638, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1328, h2638, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2641 | h2641
                    · linarith only [h1328, h2611, h2641, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1328, h2641, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h2329, h2636, hlam]
              · linarith only [h0, h2635, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2646 | h2646
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2647 | h2647
        · linarith only [h2328, h2329, h2647, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2649 | h2649
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2650 | h2650
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2651 | h2651
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2652 | h2652
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2653 | h2653
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2654 | h2654
                    · linarith only [h2647, h2654, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1328, h2654, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2329, h2646, h2652, h2653, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2658 | h2658
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2659 | h2659
                    · linarith only [h2647, h2649, h2659, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h1328, h2659, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2646, h2658, hlam]
              · linarith only [h0, h2651, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2328, h2329, h2649, h2650, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2665 | h2665
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2666 | h2666
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2667 | h2667
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2668 | h2668
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2669 | h2669
                    · linarith only [h1328, h2647, h2669, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1328, h2669, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2329, h2646, h2667, h2668, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2673 | h2673
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2674 | h2674
                    · linarith only [h1328, h2647, h2674, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1328, h2674, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2646, h2673, hlam]
              · linarith only [h0, h2666, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2329, h2646, h2665, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2680 | h2680
        · linarith only [h2328, h2329, h2680, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2682 | h2682
          · linarith only [h2328, h2646, h2680, h2682, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2684 | h2684
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2685 | h2685
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2686 | h2686
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2687 | h2687
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2688 | h2688
                    · linarith only [h2680, h2688, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1328, h2688, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2328, h2329, h2686, h2687, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2692 | h2692
                  · linarith only [h2328, h2646, h2686, h2692, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2694 | h2694
                    · linarith only [h1328, h2680, h2694, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1328, h2694, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h2685, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2698 | h2698
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2699 | h2699
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2700 | h2700
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2701 | h2701
                    · linarith only [h1328, h2680, h2701, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1328, h2701, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2329, h2699, h2700, hc02, hc25, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2705 | h2705
                  · linarith only [h2328, h2646, h2699, h2705, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2707 | h2707
                    · linarith only [h1328, h2680, h2707, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1328, h2707, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h2698, hc01, hlam, hphi, ht12, ht23, u3elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2711 | h2711
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2712 | h2712
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2713 | h2713
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2714 | h2714
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2715 | h2715
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2716 | h2716
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2717 | h2717
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2718 | h2718
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2719 | h2719
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2720 | h2720
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2721 | h2721
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2722 | h2722
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2723 | h2723
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2724 | h2724
                              · linarith only [h2328, h2711, h2716, h2724, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h2328, h2711, h2715, h2716, h2722, h2724, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h2328, h2723, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h2328, h2722, hc02, hlam, hphi, ht23, u3elo3]
                        · linarith only [h2328, h2711, h2715, h2721, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h2328, h2711, h2714, h2715, h2716, h2720, hlam]
                    · linarith only [h2328, h2716, h2719, hc02, hlam, hphi, ht23, u3elo3]
                  · linarith only [h2328, h2712, h2716, h2718, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h2328, h2716, h2717, hc02, hc24, hlam, hphi]
              · linarith only [h0, h2716, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2735 | h2735
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2736 | h2736
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2737 | h2737
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2738 | h2738
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2739 | h2739
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2740 | h2740
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2741 | h2741
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2742 | h2742
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2743 | h2743
                              · linarith only [h2711, h2715, h2743, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2745 | h2745
                                · linarith only [h2711, h2715, h2741, h2745, hlam]
                                · rcases h2bigk with h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h0, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2328, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2328, h2735, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2747_1, u3elo1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2328, h2735, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2747_1, u3elo1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h1328, h2328, hc01, hc12, hlam, hphi, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    rcases p2747_3 (m.d 0 2) (by simp) with h2756 | h2756
                                    · linarith only [h0, h2756, hlam]
                                    · linarith only [h2711, h2756, hlam]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    rcases p2747_3 (m.d 0 2) (by simp) with h2759 | h2759
                                    · linarith only [h0, h2759, hlam]
                                    · linarith only [h2712, h2759, hlam]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2712, h2741, h2743, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2735, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2735, h2741, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2747_1, u3elo1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2735, h2741, h2743, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2747_1, u3elo1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2711, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2736, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2741, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2743, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2712, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2737, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2742, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2712, h2741, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [hlam, p2747_0]
                            · linarith only [h2328, h2742, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h2328, h2711, h2741, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2779 | h2779
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2780 | h2780
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2781 | h2781
                              · linarith only [h2328, h2711, h2740, h2781, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2783 | h2783
                                · linarith only [h2328, h2712, h2740, h2779, h2781, h2783, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                · rcases h2bigk with h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c | h2785c
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h0, hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2328, hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2328, h2779, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2785_1]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2328, h2779, h2781, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2785_1, u3elo0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2785_1]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2328, h2712, h2779, h2781, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2785_1]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    rcases p2785_3 (m.d 0 2) (by simp) with h2794 | h2794
                                    · linarith only [h0, h2794, hlam]
                                    · linarith only [h2711, h2794, hlam]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    rcases p2785_3 (m.d 0 2) (by simp) with h2797 | h2797
                                    · linarith only [h0, h2797, hlam]
                                    · linarith only [h2712, h2797, hlam]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2712, h2735, h2779, h2781, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2785_1, u3elo1]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2735, hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2735, h2779, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2785_1, u3elo1]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2735, h2779, h2781, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2785_1, u3elo1]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2711, hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2736, hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2779, hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2781, hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2712, hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2737, hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2780, hlam, p2785_0]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [h2712, h2779, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2785_1]
                                  · have p2785_0 := h2785c.1
                                    have p2785_1 := h2785c.2.1
                                    have p2785_2 := h2785c.2.2.1
                                    have p2785_3 := h2785c.2.2.2
                                    linarith only [hlam, p2785_0]
                            · linarith only [h2328, h2780, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h2328, h2779, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h1328, h2739, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2328, h2711, h2735, h2738, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h2328, h2712, h2737, hc12, hc23, hlam, hphi]
                · linarith only [h2328, h2735, h2736, hc02, hc24, hlam, hphi]
              · linarith only [h0, h2735, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h2328, h2712, h2714, hlam]
        · linarith only [h2328, h2711, h2713, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2824 | h2824
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2825 | h2825
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2826 | h2826
            · linarith only [h2711, h2712, h2826, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2828 | h2828
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2829 | h2829
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2830 | h2830
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2831 | h2831
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2832 | h2832
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2833 | h2833
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2834 | h2834
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2835 | h2835
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2836 | h2836
                              · linarith only [h2711, h2712, h2826, h2836, hlam]
                              · linarith only [h2711, h2712, h2831, h2833, h2834, h2836, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h2328, h2711, h2834, h2835, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h2328, h2711, h2834, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2841 | h2841
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2842 | h2842
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2843 | h2843
                              · linarith only [h2711, h2712, h2828, h2833, h2842, h2843, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2845 | h2845
                                · linarith only [h2711, h2712, h2830, h2833, h2841, h2845, hlam]
                                · rcases h2bigk with h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c | h2847c
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h0, hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2328, hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2712, h2828, h2842, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2847_1, u3elo1]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2712, hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2847_1]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2328, h2711, h2841, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2847_1]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    rcases p2847_3 (m.d 0 2) (by simp) with h2856 | h2856
                                    · linarith only [h0, h2856, hlam]
                                    · linarith only [h2711, h2856, hlam]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2711, h2712, h2841, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2847_1]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2711, h2841, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2847_1]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2828, hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2828, h2841, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2847_1, u3elo1]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2711, h2712, h2828, h2841, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2847_1, u3elo1]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2711, hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2829, hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2841, hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2843, hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2711, h2830, h2841, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2847_1]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2830, hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2842, hlam, p2847_0]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [h2830, h2832, h2841, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2847_1, u3elo1]
                                  · have p2847_0 := h2847c.1
                                    have p2847_1 := h2847c.2.1
                                    have p2847_2 := h2847c.2.2.1
                                    have p2847_3 := h2847c.2.2.2
                                    linarith only [hlam, p2847_0]
                            · linarith only [h2825, h2842, hc23, hlam, hphi, u3elo0]
                          · linarith only [h2328, h2841, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h2328, h2711, h2825, h2828, h2832, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h2328, h2711, h2824, h2828, h2831, hlam]
                  · linarith only [h2328, h2711, h2828, h2830, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h2328, h2711, h2828, h2829, hlam]
              · linarith only [h0, h2828, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2882 | h2882
            · linarith only [h2328, h2711, h2825, h2882, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2884 | h2884
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2885 | h2885
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2886 | h2886
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2887 | h2887
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2888 | h2888
                      · linarith only [h2328, h2825, h2888, hc02, hlam, hphi, ht23, u3elo1]
                      · linarith only [h1328, h2888, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2328, h2711, h2884, h2887, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h2328, h2711, h2884, h2886, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h2328, h2711, h2884, h2885, hlam]
              · linarith only [h0, h2884, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h2328, h2711, h2824, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2896 | h2896
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2897 | h2897
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2898 | h2898
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2899 | h2899
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2900 | h2900
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2901 | h2901
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2902 | h2902
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2903 | h2903
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2904 | h2904
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2905 | h2905
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2906 | h2906
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2907 | h2907
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2908 | h2908
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2909 | h2909
                                · rcases h2bigk with h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h0, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2328, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2711, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2711, h2907, h2909, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2328, h2896, h2907, h2909, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2711, h2896, h2907, h2909, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    rcases p2910_3 (m.d 0 2) (by simp) with h2920 | h2920
                                    · linarith only [h0, h2920, hlam]
                                    · linarith only [h2896, h2920, hlam]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2896, h2907, h2909, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2900, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2711, h2896, h2900, h2907, h2909, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2910_1, u3elo1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2900, h2907, h2909, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2910_1, u3elo1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2896, h2907, h2909, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2901, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2906, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2901, h2903, h2907, h2909, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2910_1, u3elo1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2896, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2902, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2907, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2908, hlam, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [hlam, p2910_0]
                                · linarith only [h2711, h2896, h2901, h2903, h2908, h2909, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · linarith only [h2711, h2899, h2908, hlam]
                            · linarith only [h2328, h2907, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h1975, h2328, h2896, h2906, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h2711, h2896, h2899, h2901, h2905, hlam]
                      · linarith only [h2328, h2896, h2898, h2904, hc13, hlam, hphi, u3elo2]
                    · linarith only [h2328, h2897, h2900, h2903, hlam]
                  · linarith only [h2328, h2896, h2900, h2902, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h2328, h2900, h2901, hc02, hc24, hlam, hphi]
              · linarith only [h0, h2900, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2711, h2896, h2899, hlam]
          · linarith only [h2711, h2896, h2897, h2898, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2950 | h2950
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2951 | h2951
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2952 | h2952
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2953 | h2953
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2954 | h2954
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2955 | h2955
                    · linarith only [h2897, h2955, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1328, h2955, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2328, h2896, h2952, h2954, hlam]
                · linarith only [h2328, h2896, h2952, h2953, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h2952, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2328, h2896, h2897, h2951, hlam]
          · linarith only [h2328, h2896, h2950, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2963 | h2963
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2964 | h2964
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2965 | h2965
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2966 | h2966
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2967 | h2967
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2968 | h2968
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2969 | h2969
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2970 | h2970
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2971 | h2971
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2972 | h2972
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2973 | h2973
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2974 | h2974
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2975 | h2975
                                · rcases h2bigk with h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c | h2976c
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h0, hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h2328, hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h2711, hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h2896, hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2976_1]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h0, h2328, hc01, hc12, hlam, hphi, p2976_1]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h0, h2711, hc01, hc12, hlam, hphi, p2976_1]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h0, h2896, hc01, hc12, hlam, hphi, p2976_1]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2976_1]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h2966, hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h0, h2711, h2966, hc01, hlam, hphi, ht12, ht23, p2976_1, u3elo1]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h0, h2896, h2966, hc01, hlam, hphi, ht12, ht23, p2976_1, u3elo1]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h0, hc01, hc24, hlam, hphi, ht12, p2976_1]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h2967, hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h2972, hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h0, h2896, h2967, h2969, hc01, hlam, hphi, ht12, ht23, p2976_1, u3elo1]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2976_1]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h2968, hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h2973, hlam, p2976_0]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [h2974, hlam, p2976_1]
                                  · have p2976_0 := h2976c.1
                                    have p2976_1 := h2976c.2.1
                                    have p2976_2 := h2976c.2.2.1
                                    have p2976_3 := h2976c.2.2.2
                                    linarith only [hlam, p2976_0]
                                · rcases h2bigk with h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h0, hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h2328, hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h2711, hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h2896, hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p3002_1]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h0, h2328, hc01, hc12, hlam, hphi, p3002_1]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h2711, h2965, h2975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3002_1]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h0, h2896, hc01, hc12, hlam, hphi, p3002_1]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3002_1]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h2966, hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h2711, h2965, h2966, h2975, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3002_1, u3elo1]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h0, h2896, h2966, hc01, hlam, hphi, ht12, ht23, p3002_1, u3elo1]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h0, h2967, hc01, hc14, hlam, hphi, p3002_1]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h2967, hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h2972, hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h0, h2896, h2967, h2969, hc01, hlam, hphi, ht12, ht23, p3002_1, u3elo1]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3002_1]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h2968, hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h2973, hlam, p3002_0]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [h2974, hlam, p3002_1]
                                  · have p3002_0 := h3002c.1
                                    have p3002_1 := h3002c.2.1
                                    have p3002_2 := h3002c.2.2.1
                                    have p3002_3 := h3002c.2.2.2
                                    linarith only [hlam, p3002_0]
                              · linarith only [h0, h2711, h2963, h2965, h2974, hc01, hlam, hphi, ht12, ht23, u3elo0]
                            · linarith only [h0, h1975, h2328, h2964, h2969, h2971, h2973, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h0, h2328, h2972, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h2711, h2965, h2967, h2971, hlam]
                      · linarith only [h2964, h2970, hc13, hlam, hphi, u3elo0]
                    · linarith only [h2328, h2963, h2966, h2969, hlam]
                  · linarith only [h0, h2328, h2966, h2968, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2328, h2966, h2967, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h2966, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3037 | h3037
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3038 | h3038
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3039 | h3039
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3040 | h3040
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3041 | h3041
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3042 | h3042
                        · linarith only [h2711, h2965, h3040, h3042, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3044 | h3044
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3045 | h3045
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3046 | h3046
                              · linarith only [h3038, h3042, h3046, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3048 | h3048
                                · linarith only [h0, h2711, h3038, h3042, h3048, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                · rcases h2bigk with h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c | h3050c
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h0, hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h2328, hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h2711, hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h2896, hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p3050_1]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h2328, h2964, h3048, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3050_1]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h0, h2711, hc01, hc12, hlam, hphi, p3050_1]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h0, h2896, hc01, hc12, hlam, hphi, p3050_1]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3050_1]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h3037, hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h0, h2711, h3037, hc01, hlam, hphi, ht12, ht23, p3050_1, u3elo1]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h0, h2896, h3037, hc01, hlam, hphi, ht12, ht23, p3050_1, u3elo1]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h0, h3038, hc01, hc14, hlam, hphi, p3050_1]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h3038, hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h3044, hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h3046, hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3050_1]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h3039, hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h3045, hlam, p3050_0]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [h3039, h3041, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3050_1, u3elo1]
                                  · have p3050_0 := h3050c.1
                                    have p3050_1 := h3050c.2.1
                                    have p3050_2 := h3050c.2.2.1
                                    have p3050_3 := h3050c.2.2.2
                                    linarith only [hlam, p3050_0]
                            · linarith only [h2964, h3045, hc23, hlam, hphi, u3elo0]
                          · linarith only [h0, h2328, h3044, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h2328, h2964, h3037, h3041, hlam]
                    · linarith only [h2328, h2963, h3037, h3040, hlam]
                  · linarith only [h0, h2328, h3037, h3039, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2328, h3037, h3038, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3037, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3083 | h3083
            · linarith only [h2963, h2964, h3083, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3085 | h3085
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3086 | h3086
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3087 | h3087
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3088 | h3088
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3089 | h3089
                      · linarith only [h2964, h3089, hc03, hlam, hphi, u3elo1]
                      · linarith only [h1328, h3089, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h2328, h3085, h3088, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2328, h3085, h3087, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2328, h3085, h3086, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3085, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3096 | h3096
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3097 | h3097
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3098 | h3098
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3099 | h3099
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3100 | h3100
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3101 | h3101
                    · linarith only [h2963, h3101, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1328, h3101, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2328, h3098, h3100, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2328, h3098, h3099, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3098, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2963, h3096, h3097, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3108 | h3108
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3109 | h3109
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3110 | h3110
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3111 | h3111
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3112 | h3112
                    · linarith only [h2963, h3112, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1328, h3112, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2328, h3109, h3111, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2328, h3109, h3110, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3109, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3118 | h3118
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3119 | h3119
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3120 | h3120
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3121 | h3121
                    · linarith only [h0, h2328, h2963, h3121, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1328, h3121, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2328, h3118, h3120, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2328, h3118, h3119, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3118, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1328 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1975 | h1975
  · exact r1l7_22_13_15_H_I_L_0_L_I_x1_x1_x0 m hb2 hb3 hb5 h0 h1328 h1975
  · exact r1l7_22_13_15_H_I_L_0_L_I_x1_x1_x1 m hb2 hb3 hb5 h0 h1328 h1975

set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1328 | h1328
  · exact r1l7_22_13_15_H_I_L_0_L_I_x1_x0 m hb2 hb3 hb5 h0 h1328
  · exact r1l7_22_13_15_H_I_L_0_L_I_x1_x1 m hb2 hb3 hb5 h0 h1328

set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_13_15_H_I_L_0_L_I_x0 m hb2 hb3 hb5 h0
  · exact r1l7_22_13_15_H_I_L_0_L_I_x1 m hb2 hb3 hb5 h0

end R2N4
